import Lean.Elab.Tactic.Meta
import Lean.Meta.Closure
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Intro

open Lean Meta Elab Tactic

private def extractPrefix (type proof : Expr) : List (MVarId × Expr) → MetaM Expr
  | [] => do
    let proof ← instantiateMVars proof
    if proof.hasMVar then throwError "proof_step: unresolved prefix metavariables"
    mkAuxTheorem type proof (zetaDelta := true)
  | (pending, continuation) :: rest => do
    withLocalDeclD `_continuation (← pending.getType) fun hypothesis => do
      pending.assign hypothesis
      let result ← extractPrefix type proof rest
      return result.replaceFVar hypothesis continuation

elab "proof_step" " => " body:tacticSeq : tactic => withMainContext do
  let goal ← getMainGoal
  let originalContext ← getLCtx
  let piece ← mkFreshExprSyntheticOpaqueMVar (← goal.getType)
  let remaining ← Tactic.run piece.mvarId! (evalTactic body)
  let continuations ← remaining.mapM fun next => next.withContext do
    let extras := (← getLCtx).getFVarIds.filter (!originalContext.contains ·)
    let (reverted, pending) ← next.revert extras (preserveOrder := true)
    let continuation ← pending.withContext do
      mkFreshExprSyntheticOpaqueMVar (← pending.getType)
    return (pending, continuation, reverted.size)
  let context ← getMCtx
  let proof ← extractPrefix (← goal.getType) piece
    (continuations.map fun (pending, continuation, _) => (pending, continuation))
  setMCtx context
  for (pending, continuation, _) in continuations do
    pending.assign continuation
  goal.assign proof
  let remaining ← continuations.mapM fun (_, continuation, count) => do
    let (_, next) ← continuation.mvarId!.introNP count
    return next
  replaceMainGoal remaining

example (p q : Prop) (hp : p) (hq : p → q) : q ∧ p := by
  proof_step =>
    constructor
  · proof_step =>
      apply hq
    exact hp
  · exact hp

example (p : Nat → Prop) (h : ∀ n, p n) : ∀ n, p n := by
  proof_step =>
    intro n
  exact h n

example (n : Nat) : ∃ m, m = n+1 := by
  let m := n+1
  proof_step =>
    refine ⟨m, ?_⟩
  rfl

example : ∃ n : Nat, n = 7 := by
  proof_step =>
    refine ⟨?_, ?_⟩
  · exact 7
  · rfl
