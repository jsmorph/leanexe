import LeanExe.Extract.ScalarGuardSyntax
import LeanExe.Source.ScalarDependentBranch

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar

/-- Check the standard decision expression and both proof-lambda domains.
The entire guard tree is shared with ordinary conditional compilation. -/
def dependentGuard? (condition evidence trueDomain falseDomain : Lean.Expr) : Option Guard := do
  let guard ← guardOperands? condition
  if LeanExe.Source.ExprEquality.same evidence guard.evidence &&
      LeanExe.Source.ExprEquality.same trueDomain guard.condition &&
      LeanExe.Source.ExprEquality.same falseDomain (.app (.const ``Not []) guard.condition)
    then some guard else none

@[simp] theorem dependentGuard_accepts (guard : Guard) :
    dependentGuard? guard.condition guard.evidence guard.condition
      (.app (.const ``Not []) guard.condition) = some guard := by
  simp [dependentGuard?]

theorem dependentGuard_sound {condition evidence trueDomain falseDomain : Lean.Expr} {guard : Guard}
    (parsed : dependentGuard? condition evidence trueDomain falseDomain = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence ∧
      trueDomain = guard.condition ∧ falseDomain = .app (.const ``Not []) guard.condition := by
  simp only [dependentGuard?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨shape, found, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    simp only [Bool.and_eq_true, LeanExe.Source.ExprEquality.same_eq_true] at same
    exact ⟨guardOperands_sound found, same.1.1, same.1.2, same.2⟩
  · contradiction

theorem dependentGuard_size {condition evidence trueDomain falseDomain : Lean.Expr} {guard : Guard}
    (parsed : dependentGuard? condition evidence trueDomain falseDomain = some guard)
    {operand : Lean.Expr} (member : operand ∈ guard.operands) : sizeOf operand < sizeOf condition := by
  rw [(dependentGuard_sound parsed).1]
  exact guard.operands_size member

end LeanExe.Extract.Core
