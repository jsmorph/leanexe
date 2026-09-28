import LeanExe.Core.Program
import Lean

namespace LeanExe.Core

/-- Pure source functions have no observable effects. -/
def noEffects : Effects Unit := fun _ _ _ _ _ => False

theorem Eval.call_of_invokes
    {functions : Module} {effects : Effects σ}
    {expressions : List Wasm.ScalarDescriptor.Expr} {locals result : Locals}
    {initial final : σ} {callee destination : Nat} {args : List UInt64} {value : UInt64}
    (inputs : arguments expressions locals = some args)
    (called : Invokes functions effects callee initial args final value)
    (written : IR.ScalarStore.write locals destination value = some result) :
    Eval functions effects (.call destination callee expressions) initial locals final result := by
  obtain ⟨function, returned, found, arity, executed, output⟩ := called
  exact .call found inputs arity executed output written

theorem Invokes.of_body
    {functions : Module} {effects : Effects σ} {callee : Nat}
    {initial final : σ} {args : List UInt64} {value : UInt64}
    {function : Function} {returned : Locals}
    (found : functions[callee]? = some function)
    (arity : args.length = function.params)
    (executed : Eval functions effects function.body initial
      (args ++ List.replicate function.locals 0) final returned)
    (output : function.result.eval returned = some value) :
    Invokes functions effects callee initial args final value :=
  ⟨function, returned, found, arity, executed, output⟩

/-- The value field is an ordinary Lean function. Its certificate states that
the generated core module returns that function's value for every argument. -/
def Native : Nat → Type
  | 0 => UInt64
  | n + 1 => UInt64 → Native n

def applyNative : {n : Nat} → Native n → List UInt64 → UInt64
  | 0, value, _ => value
  | n + 1, function, args => applyNative (n := n) (function (args.headD 0)) args.tail

structure NativeCertificate {arity : Nat} (function : Native arity) where
  source : Module
  entry : Nat
  correct : ∀ args, args.length = arity →
    Invokes source noEffects entry () args () (applyNative function args)

/-- Projection form keeps native state computations intact while exposing their continuation. -/
theorem state_bind_apply (action : StateM σ α) (next : α → StateM σ β) (initial : σ) :
    (action >>= next) initial = next (action initial).1 (action initial).2 := by
  change (match action initial with | (value, state) => next value state) = _
  cases action initial
  rfl

theorem state_pure_apply (value : α) (initial : σ) :
    (pure value : StateM σ α) initial = (value, initial) := rfl

theorem pair_first (value : α) (state : σ) : (value, state).1 = value := rfl

theorem pair_second (value : α) (state : σ) : (value, state).2 = state := rfl

end LeanExe.Core

open Lean Elab Tactic

syntax "core_native_eval" : tactic
syntax "core_native_invokes" : tactic

private def solveNativeCondition : TacticM Unit := withMainContext do
  let goal :: remaining ← getGoals | throwError "Expected a source condition goal"
  setGoals [goal]
  evalTactic (← `(tactic| simp_all (config := { zetaDelta := true })
    [LeanExe.Wasm.ScalarDescriptor.Cond.eval,
    LeanExe.Wasm.ScalarDescriptor.Expr.eval,
    LeanExe.Wasm.ScalarDescriptor.U64Op.apply,
    LeanExe.IR.ScalarStore.write]))
  unless (← getUnsolvedGoals).isEmpty do
    evalTactic (← `(tactic| try assumption))
  unless (← getUnsolvedGoals).isEmpty do
    throwError "Could not establish the native branch condition:\n{← Lean.Meta.ppGoal (← getMainGoal)}"
  setGoals remaining

/-- Construct evaluation proofs by the compiled statement's constructor. -/
private partial def proveNativeEval : TacticM Unit := withMainContext do
  let target ← Lean.Meta.whnf (← (← getMainGoal).getType)
  unless target.getAppFn.isConstOf ``LeanExe.Core.Eval do
    throwError "Expected a core evaluation: {target}"
  let statement ← Lean.Meta.whnf target.getAppArgs[3]!
  match statement.getAppFn.constName? with
  | some ``LeanExe.Core.Stmt.skip =>
    evalTactic (← `(tactic| exact LeanExe.Core.Eval.skip))
  | some ``LeanExe.Core.Stmt.assign =>
    evalTactic (← `(tactic| apply LeanExe.Core.Eval.assign))
    evalTactic (← `(tactic| rfl))
    evalTactic (← `(tactic| rfl))
  | some ``LeanExe.Core.Stmt.seq =>
    evalTactic (← `(tactic| apply LeanExe.Core.Eval.seq))
    proveNativeEval
    proveNativeEval
  | some ``LeanExe.Core.Stmt.branch =>
    let saved ← saveState
    try
      evalTactic (← `(tactic| apply LeanExe.Core.Eval.yes))
      solveNativeCondition
    catch _ =>
      saved.restore
      evalTactic (← `(tactic| apply LeanExe.Core.Eval.no))
      solveNativeCondition
    proveNativeEval
  | some ``LeanExe.Core.Stmt.call =>
    evalTactic (← `(tactic| apply LeanExe.Core.Eval.call_of_invokes))
    evalTactic (← `(tactic| rfl))
    evalTactic (← `(tactic| first | assumption | solve_by_elim))
    evalTactic (← `(tactic| rfl))
  | some ``LeanExe.Core.Stmt.effect =>
    evalTactic (← `(tactic| apply LeanExe.Core.Eval.effect))
    evalTactic (← `(tactic| rfl))
    evalTactic (← `(tactic| solve_by_elim))
    evalTactic (← `(tactic| rfl))
  | _ => throwError "Native proof construction does not handle this statement: {statement}"

elab_rules : tactic
| `(tactic| core_native_eval) => proveNativeEval

private partial def nativeConditional? (expression : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  let type ← Lean.Meta.inferType expression
  if type.isSort || type.isAppOfArity ``Decidable 1 || (← Lean.Meta.isProp type) then
    return none
  if expression.isAppOfArity ``ite 5 || expression.isAppOfArity ``dite 5 then
    return some expression
  match expression with
  | .app function argument =>
      if let some selected ← nativeConditional? function then return some selected
      nativeConditional? argument
  | .mdata _ body | .proj _ _ body => nativeConditional? body
  | .letE _ _ value body _ => nativeConditional? (body.instantiate1 value)
  | _ => return none

private def knownNativeCondition? (condition : Lean.Expr) : Lean.MetaM (Option (Bool × Lean.Expr)) := do
  for declaration in ← Lean.getLCtx do
    unless declaration.isImplementationDetail do
      if ← Lean.Meta.isDefEq declaration.type condition then
        return some (true, declaration.toExpr)
      if ← Lean.Meta.isDefEq declaration.type (Lean.mkNot condition) then
        return some (false, declaration.toExpr)
  return none

private def rewriteNativeConditional (goal : Lean.MVarId) (selected : Lean.Expr)
    (positive : Bool) (hypothesis : Lean.Expr) : Lean.MetaM Lean.MVarId := goal.withContext do
  let args := selected.getAppArgs
  let lemma := if selected.isAppOfArity ``ite 5 then
    if positive then ``ite_eq_left else ``ite_eq_right
  else if positive then ``dite_eq_left else ``dite_eq_right
  let equality ← Lean.Meta.mkAppOptM lemma #[some args[1]!, some args[2]!, some hypothesis,
    some args[0]!, some args[3]!, some args[4]!]
  let before ← goal.getType
  let rewritten ← goal.rewrite before equality
  unless rewritten.mvarIds.isEmpty do
    throwError "Native conditional rewrite introduced unresolved proof obligations"
  if rewritten.eNew == before then
    throwError "Native conditional rewrite made no progress on {args[1]!}"
  goal.replaceTargetEq rewritten.eNew rewritten.eqProof

/-- Split native result conditions before introducing the source's intermediate
locals. Each branch can then construct its own evaluation witnesses. -/
private partial def proveNativeInvokes (normalize : Bool := true) : TacticM Unit := withMainContext do
  let goal :: remaining ← getGoals | throwError "Expected a native invocation goal"
  setGoals [goal]
  if normalize then
    evalTactic (← `(tactic| simp (config := { proj := false, iota := false, dsimp := false, failIfUnchanged := false }) only
      [LeanExe.Core.state_bind_apply, LeanExe.Core.state_pure_apply,
        LeanExe.Core.pair_first, LeanExe.Core.pair_second]))
  let current ← getMainGoal
  let target := (← instantiateMVars (← current.getType)).cleanupAnnotations
  let arguments := target.getAppArgs
  unless target.getAppFn'.isConstOf ``LeanExe.Core.Invokes && arguments.size ≥ 2 do
    throwError "Expected a native invocation after state normalization: {target}"
  let resultCondition ← nativeConditional? arguments[arguments.size - 1]!
  let selected ← match resultCondition with
    | some expression => pure (some expression)
    | none => nativeConditional? arguments[arguments.size - 2]!
  if let some selected := selected then
    let args := selected.getAppArgs
    let condition := args[1]!
    if let some (positive, hypothesis) ← knownNativeCondition? condition then
      let next ← rewriteNativeConditional current selected positive hypothesis
      setGoals [next]
      proveNativeInvokes false
      setGoals ((← getUnsolvedGoals) ++ remaining)
    else
      let (yes, no) ← current.byCasesDec condition args[2]!
      let branches := [(yes, true), (no, false)]
      let mut unfinished := []
      for (branch, positive) in branches do
        let next ← rewriteNativeConditional branch.mvarId selected positive (.fvar branch.fvarId)
        setGoals [next]
        proveNativeInvokes false
        unfinished := unfinished ++ (← getUnsolvedGoals)
      setGoals (unfinished ++ remaining)
  else
    evalTactic (← `(tactic| apply LeanExe.Core.Invokes.of_body))
    evalTactic (← `(tactic| rfl))
    evalTactic (← `(tactic| rfl))
    proveNativeEval
    evalTactic (← `(tactic| first
      | rfl
      | simp_all [LeanExe.Wasm.ScalarDescriptor.Expr.eval,
          LeanExe.Wasm.ScalarDescriptor.U64Op.apply, StateT.bind, StateT.pure,
          Bind.bind, Pure.pure]))
    setGoals ((← getUnsolvedGoals) ++ remaining)

elab_rules : tactic
| `(tactic| core_native_invokes) => proveNativeInvokes true
