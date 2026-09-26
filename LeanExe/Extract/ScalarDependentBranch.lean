import LeanExe.Extract.ScalarGuardSyntax
import LeanExe.Source.ScalarDependentBranch

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar

/-- Check standard decision evidence and both exact proof-lambda domains. -/
def dependentGuard? (condition evidence trueDomain falseDomain : Lean.Expr) : Option DecidedGuard := do
  let tree ← guardOperands? condition
  if accepted : guardDecision? tree evidence = true then
    if LeanExe.Source.ExprEquality.same trueDomain tree.condition &&
        LeanExe.Source.ExprEquality.same falseDomain (.app (.const ``Not []) tree.condition)
      then some ⟨tree, evidence, guardDecision_sound accepted⟩ else none
  else none

@[simp] theorem dependentGuard_accepts (guard : DecidedGuard) :
    dependentGuard? guard.condition guard.evidence guard.condition
      (.app (.const ``Not []) guard.condition) = some guard := by
  cases guard with
  | mk tree evidence meaning =>
    simp [dependentGuard?, DecidedGuard.condition, guardDecision_accepts meaning]

theorem dependentGuard_sound {condition evidence trueDomain falseDomain : Lean.Expr} {guard : DecidedGuard}
    (parsed : dependentGuard? condition evidence trueDomain falseDomain = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence ∧
      trueDomain = guard.condition ∧ falseDomain = .app (.const ``Not []) guard.condition := by
  simp only [dependentGuard?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨tree, found, accepted⟩ := parsed
  split at accepted
  · split at accepted
    · rename_i same
      cases accepted
      simp only [Bool.and_eq_true, LeanExe.Source.ExprEquality.same_eq_true] at same
      exact ⟨guardOperands_sound found, rfl, same.1, same.2⟩
    · contradiction
  · contradiction

theorem dependentGuard_size {condition evidence trueDomain falseDomain : Lean.Expr} {guard : DecidedGuard}
    (parsed : dependentGuard? condition evidence trueDomain falseDomain = some guard)
    {operand : Lean.Expr} (member : operand ∈ guard.operands) : sizeOf operand < sizeOf condition := by
  rw [(dependentGuard_sound parsed).1]
  exact guard.operands_size member

end LeanExe.Extract.Core
