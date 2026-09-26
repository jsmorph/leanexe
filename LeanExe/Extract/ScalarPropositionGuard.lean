import LeanExe.Source.ScalarPropositionGuard
import LeanExe.Extract.ScalarGuardSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def propositionGuard? (condition evidence : Lean.Expr) : Option PropositionGuard := do
  let guard ← guardOperands? condition
  if nonboolean : guard.hasBooleanCondition = false then
    if accepted : guardDecision? guard evidence = true then
      some ⟨⟨guard, evidence, guardDecision_sound accepted⟩, nonboolean⟩
    else none
  else none

@[simp] theorem propositionGuard_accepts (guard : PropositionGuard) :
    propositionGuard? guard.condition guard.evidence = some guard := by
  cases guard with
  | mk value nonboolean =>
    cases value with
    | mk tree evidence meaning =>
      simp [propositionGuard?, PropositionGuard.condition, PropositionGuard.evidence,
        DecidedGuard.condition, nonboolean, guardDecision_accepts meaning]

theorem propositionGuard_sound {condition evidence : Lean.Expr} {guard : PropositionGuard}
    (parsed : propositionGuard? condition evidence = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence := by
  simp only [propositionGuard?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨value, found, accepted⟩ := parsed
  split at accepted
  · split at accepted
    · rename_i same
      cases accepted
      exact ⟨guardOperands_sound found, rfl⟩
    · contradiction
  · contradiction

theorem propositionGuard_size {condition evidence : Lean.Expr} {guard : PropositionGuard}
    (parsed : propositionGuard? condition evidence = some guard) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf condition := by
  rw [(propositionGuard_sound parsed).1]
  exact guard.value.operands_size member

end LeanExe.Extract.Core
