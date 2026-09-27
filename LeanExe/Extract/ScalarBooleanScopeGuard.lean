import LeanExe.Source.ScalarBooleanScopeGuard
import LeanExe.Extract.ScalarBooleanHelper
import LeanExe.Extract.ScalarBooleanLocalDependentBranch

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

@[simp] theorem booleanScopeGuard_not_local (guard : BooleanScopeGuard) :
    booleanLocalOperands? guard.value.expr = none := by
  cases found : booleanLocalOperands? guard.value.expr with
  | none => rfl
  | some expression => exact False.elim (guard.extended expression (booleanLocalOperands_sound found))

def booleanScopeGuard? (condition evidence : Lean.Expr) : Option BooleanScopeGuard := do
  let value ← savedBooleanGuard? condition
  if absent : booleanLocalOperands? value.expr = none then
    if LeanExe.Source.ExprEquality.same evidence value.evidence then
      some ⟨value, booleanLocal_excluded absent⟩
    else none
  else none

@[simp] theorem booleanScopeGuard_accepts (guard : BooleanScopeGuard) :
    booleanScopeGuard? guard.condition guard.evidence = some guard := by
  have absent := booleanScopeGuard_not_local guard
  cases guard
  simp [booleanScopeGuard?, BooleanScopeGuard.condition, BooleanScopeGuard.evidence, absent]

theorem booleanScopeGuard_sound {condition evidence : Lean.Expr} {guard : BooleanScopeGuard}
    (parsed : booleanScopeGuard? condition evidence = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence := by
  simp only [booleanScopeGuard?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨value, found, accepted⟩ := parsed
  split at accepted
  · split at accepted
    · rename_i same
      cases accepted
      exact ⟨savedBooleanGuard_sound found, LeanExe.Source.ExprEquality.same_eq_true.mp same⟩
    · contradiction
  · contradiction

theorem booleanScopeGuard_size {condition evidence : Lean.Expr} {guard : BooleanScopeGuard}
    (parsed : booleanScopeGuard? condition evidence = some guard) : sizeOf guard.operand < sizeOf condition := by
  rw [(booleanScopeGuard_sound parsed).1]
  exact guard.operand_size

@[simp] theorem booleanScopeGuard_not_comparison (guard : BooleanScopeGuard) :
    comparison? guard.condition guard.evidence = none := by
  have absent := booleanTruth_not_comparison_of_not_closed guard.value.value guard.value.extended
  change comparisonOperands? guard.value.condition = none at absent
  simp [comparison?, BooleanScopeGuard.condition, absent]

@[simp] theorem booleanScopeGuard_not_compound (guard : BooleanScopeGuard) :
    compoundGuard? guard.condition guard.evidence = none :=
  compoundGuard_none_of_no_guard (savedBooleanGuard_not_guard guard.value)

@[simp] theorem booleanScopeGuard_not_boolean (guard : BooleanScopeGuard) :
    booleanLocalGuard? guard.condition guard.evidence = none := by
  simp [booleanLocalGuard?, BooleanScopeGuard.condition, SavedBooleanGuard.condition]

def booleanScopeDependentGuard? (condition evidence trueDomain falseDomain : Lean.Expr) :
    Option BooleanScopeGuard := do
  let guard ← booleanScopeGuard? condition evidence
  if LeanExe.Source.ExprEquality.same trueDomain guard.condition &&
      LeanExe.Source.ExprEquality.same falseDomain (.app (.const ``Not []) guard.condition)
    then some guard else none

@[simp] theorem booleanScopeDependentGuard_accepts (guard : BooleanScopeGuard) :
    booleanScopeDependentGuard? guard.condition guard.evidence guard.condition
      (.app (.const ``Not []) guard.condition) = some guard := by
  simp [booleanScopeDependentGuard?]

theorem booleanScopeDependentGuard_sound {condition evidence trueDomain falseDomain : Lean.Expr}
    {guard : BooleanScopeGuard}
    (parsed : booleanScopeDependentGuard? condition evidence trueDomain falseDomain = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence ∧
      trueDomain = guard.condition ∧ falseDomain = .app (.const ``Not []) guard.condition := by
  simp only [booleanScopeDependentGuard?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨guard, found, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    simp only [Bool.and_eq_true, LeanExe.Source.ExprEquality.same_eq_true] at same
    exact ⟨(booleanScopeGuard_sound found).1, (booleanScopeGuard_sound found).2, same.1, same.2⟩
  · contradiction

theorem booleanScopeDependentGuard_size {condition evidence trueDomain falseDomain : Lean.Expr}
    {guard : BooleanScopeGuard}
    (parsed : booleanScopeDependentGuard? condition evidence trueDomain falseDomain = some guard) :
    sizeOf guard.operand < sizeOf condition := by
  rw [(booleanScopeDependentGuard_sound parsed).1]
  exact guard.operand_size

@[simp] theorem booleanScopeGuard_not_dependent (guard : BooleanScopeGuard) (td fd : Lean.Expr) :
    dependentGuard? guard.condition guard.evidence td fd = none := by
  simp [dependentGuard?, BooleanScopeGuard.condition, savedBooleanGuard_not_guard]

@[simp] theorem booleanScopeGuard_not_booleanDependent (guard : BooleanScopeGuard) (td fd : Lean.Expr) :
    booleanLocalDependentGuard? guard.condition guard.evidence td fd = none := by
  simp [booleanLocalDependentGuard?]

end LeanExe.Extract.Core
