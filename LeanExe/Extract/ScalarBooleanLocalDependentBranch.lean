import LeanExe.Extract.ScalarBooleanLocalSyntax
import LeanExe.Extract.ScalarDependentBranch

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Dependent Boolean-local conditions retain the same exact decision and
proof-domain requirements as closed dependent guards. -/
def booleanLocalDependentGuard? (condition evidence trueDomain falseDomain : Lean.Expr) :
    Option BooleanLocalGuard := do
  let guard ← booleanLocalGuard? condition evidence
  if LeanExe.Source.ExprEquality.same trueDomain guard.condition &&
      LeanExe.Source.ExprEquality.same falseDomain (.app (.const ``Not []) guard.condition)
    then some guard else none

@[simp] theorem booleanLocalDependentGuard_accepts (guard : BooleanLocalGuard) :
    booleanLocalDependentGuard? guard.condition guard.evidence guard.condition
      (.app (.const ``Not []) guard.condition) = some guard := by
  simp [booleanLocalDependentGuard?]

theorem booleanLocalDependentGuard_sound {condition evidence trueDomain falseDomain : Lean.Expr}
    {guard : BooleanLocalGuard}
    (parsed : booleanLocalDependentGuard? condition evidence trueDomain falseDomain = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence ∧
      trueDomain = guard.condition ∧ falseDomain = .app (.const ``Not []) guard.condition := by
  simp only [booleanLocalDependentGuard?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨shape, found, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    simp only [Bool.and_eq_true, LeanExe.Source.ExprEquality.same_eq_true] at same
    exact ⟨(booleanLocalGuard_sound found).1, (booleanLocalGuard_sound found).2, same.1, same.2⟩
  · contradiction

theorem booleanLocalDependentGuard_not_closed (guard : BooleanLocalGuard) (td fd : Lean.Expr) :
    dependentGuard? guard.condition guard.evidence td fd = none := by
  simp [dependentGuard?, booleanLocal_not_guard]

theorem booleanLocalDependentGuard_size {condition evidence trueDomain falseDomain : Lean.Expr}
    {guard : BooleanLocalGuard}
    (parsed : booleanLocalDependentGuard? condition evidence trueDomain falseDomain = some guard)
    {operand : Lean.Expr} (member : operand ∈ guard.value.operands) : sizeOf operand < sizeOf condition := by
  rw [(booleanLocalDependentGuard_sound parsed).1]
  have bound := guard.value.operands_size member
  simp only [BooleanLocalGuard.condition, BooleanLocal.condition]
  simp_all; omega

end LeanExe.Extract.Core
