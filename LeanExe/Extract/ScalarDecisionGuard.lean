import LeanExe.Extract.ScalarGuardSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- A closed guard with the complete standard decision expression. -/
def decisionGuard? (condition evidence : Lean.Expr) : Option Guard := do
  let guard ← guardOperands? condition
  if LeanExe.Source.ExprEquality.same evidence guard.evidence then some guard else none

@[simp] theorem decisionGuard_accepts (guard : Guard) :
    decisionGuard? guard.condition guard.evidence = some guard := by
  simp [decisionGuard?]

theorem decisionGuard_sound {condition evidence : Lean.Expr} {guard : Guard}
    (parsed : decisionGuard? condition evidence = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence := by
  simp only [decisionGuard?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨value, found, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    exact ⟨guardOperands_sound found, LeanExe.Source.ExprEquality.same_eq_true.mp same⟩
  · contradiction

end LeanExe.Extract.Core
