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
  | _ => throwError "Native proof construction does not handle this statement: {statement}"

elab_rules : tactic
| `(tactic| core_native_eval) => proveNativeEval

elab_rules : tactic
| `(tactic| core_native_invokes) => withMainContext do
  evalTactic (← `(tactic| apply LeanExe.Core.Invokes.of_body))
  evalTactic (← `(tactic| rfl))
  evalTactic (← `(tactic| rfl))
  evalTactic (← `(tactic| core_native_eval))
  evalTactic (← `(tactic| first
    | rfl
    | simp_all [LeanExe.Wasm.ScalarDescriptor.Expr.eval,
        LeanExe.Wasm.ScalarDescriptor.U64Op.apply]))
