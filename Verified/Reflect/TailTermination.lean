module

public import Verified.Reflect.TailBody
public import Verified.TailTransport

@[expose] public section

namespace Verified.Reflect

open Lean Meta Elab Term

def tailRelation (step stateType resultType : Lean.Expr) : MetaM Lean.Expr := do
  withLocalDeclD `next stateType fun next => withLocalDeclD `state stateType fun state => do
    let continuation ← mkAppOptM ``Sum.inl #[some stateType, some resultType, some next]
    mkLambdaFVars #[next, state] (← mkEq (mkApp step state) continuation)

/-- The goal with each local definition replaced by its value in the hypotheses and the target, and
cleared.  A `let` of the source, such as `let r := part …`, is a local definition in the cases of
functional induction, whose hypotheses state conditions on the local where the step states them on
its value. -/
def unfoldLocalDefinitions (goal : MVarId) : MetaM MVarId := goal.withContext do
  let lets := (← getLCtx).foldl (init := #[]) fun lets decl =>
    if decl.isLet && !decl.isImplementationDetail then lets.push decl.fvarId else lets
  if lets.isEmpty then return goal
  let mut goal := goal
  for decl in ← getLCtx do
    unless decl.isLet || decl.isImplementationDetail do
      goal ← goal.replaceLocalDeclDefEq decl.fvarId
        (← zetaDeltaFVars (← instantiateMVars decl.type) lets)
  goal ← goal.replaceTargetDefEq
    (← zetaDeltaFVars (← instantiateMVars (← goal.getType)) lets)
  goal.tryClearMany lets

def deriveTailAcc (name stepName : Name) (params : Array Lean.Expr)
    (stateType resultType : Lean.Expr) : TermElabM Lean.Expr := do
  let some _ ← getFunIndInfo? false false name
    | throwError "verified_compile: {name} has no functional induction theorem"
  let relation ← tailRelation (mkConst stepName) stateType resultType
  let state ← argsTuple (params.toList.map (·, false))
  let goal ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Acc #[relation, state])
  let app ← exprToSyntax (mkAppN (mkConst name) params)
  let stepId := mkIdent stepName
  -- A case whose step equation keeps an `if` that the case's hypotheses decide only in another
  -- form, such as `r ≤ 1 ∨ d ≤ 1` against `1 < r ∧ 1 < d`, splits the equation on its `if`s.  A
  -- branch whose condition contradicts the case's hypotheses closes by `omega` on the words'
  -- natural numbers and on the integers of `Int64` values.
  let script ← `(tactic|
    (refine Acc.intro _ ?_; intro next hs; simp_all [$stepId:ident]) <;>
      try ((repeat' split at hs) <;> try simp_all) <;>
      try ((simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.reduceToNat,
          Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le, Int64.reduceToInt] at *)
        <;> omega))
  let cases ← Tactic.run goal.mvarId! <| Tactic.evalTactic (← `(tactic| fun_induction $app))
  let remaining ← cases.flatMapM fun case => do
    Tactic.run (← unfoldLocalDefinitions case) (Tactic.evalTactic script)
  unless remaining.isEmpty do
    let goals := MessageData.joinSep (remaining.map MessageData.ofGoal) "\n"
    throwError "verified_compile: the tail transition of {name} has unproved induction cases:\n{goals}"
  let proof ← instantiateMVars goal
  if proof.hasExprMVar then
    throwError "verified_compile: the termination proof of {name} has unresolved arguments"
  return proof

def tailWellFounded (step : Lean.Expr) (params : Array Lean.Expr) (types : List Ty)
    (stateType resultType : Lean.Expr) (acc : Lean.Expr) : MetaM Lean.Expr := do
  let relation ← tailRelation step stateType resultType
  let curried ← mkLambdaFVars params acc
  let all ← withLocalDeclD `state stateType fun state => do
    let values ← argProjsE state (types.map fun _ => .borrowed) types.length
    let proof := mkAppN curried values.toArray
    mkLambdaFVars #[state] (← mkExpectedTypeHint proof (← mkAppM ``Acc #[relation, state]))
  mkAppM ``WellFounded.intro #[all]

/-- Adds the theorem `name : type` with the proof that `prove` computes on an environment branch of
its own, as the elaborator does for the proof of a `theorem` (`Lean.Elab.Term.elabMutualDef`).
The functional induction principles that `deriveTailAcc` realizes then stay with the proof.
Realized on the command's branch, they would join this module's public interface as axioms, and
Lean v4.36.0 refuses to import two modules that hold such axioms for the same function: it merges
two exported axioms only when the conclusion starts with a constant, and these conclude in their
motive.  Lean v4.36.0 exports a principle realized on a proof's branch as a theorem, which it
merges, and later versions do not export it (lean4#16623). -/
def addTheoremOnBranch (name : Name) (type : Lean.Expr) (prove : TermElabM Lean.Expr) :
    TermElabM Unit := do
  let env ← getEnv
  let env := if env.header.isModule then recordOriginalConstKind env name .thm else env
  let async ← env.addConstAsync name .thm (exportedKind? := some .axiom)
  async.commitSignature { name, levelParams := [], type }
  setEnv async.asyncEnv
  try
    let value ← prove
    addDecl <| .thmDecl { name, levelParams := [], type, value }
    async.commitConst (← getEnv)
    async.commitCheckEnv (← getEnv)
  finally
    setEnv async.mainEnv

end Verified.Reflect
