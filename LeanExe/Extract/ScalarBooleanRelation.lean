import LeanExe.Source.ScalarBooleanLocal
import LeanExe.Extract.ScalarGuardSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

theorem booleanRelationEqual_not_comparison (left right : Lean.Expr)
    (nontrue : right ≠ .const ``Bool.true []) :
    comparisonOperands? (booleanRelationCondition false left right) = none := by
  simp [booleanRelationCondition, comparisonOperands?, scalarResultType?, nontrue]

theorem booleanRelationUnequal_not_comparison (left right : Lean.Expr) :
    comparisonOperands? (booleanRelationCondition true left right) = none := by
  rfl

theorem booleanRelationEqual_not_guard (left right : Lean.Expr)
    (nontrue : right ≠ .const ``Bool.true []) :
    guardOperands? (booleanRelationCondition false left right) = none := by
  rw [guardOperands?]
  · rw [booleanRelationEqual_not_comparison left right nontrue]
    simp only [booleanGuardCondition?, booleanRelationCondition]
    split <;> simp_all
  all_goals simp [booleanRelationCondition]

theorem booleanRelationUnequal_not_guard (left right : Lean.Expr) :
    guardOperands? (booleanRelationCondition true left right) = none := by
  rfl

theorem propositionGuard_not_boolean_equal (guard : PropositionGuard) (left right : Lean.Expr) :
    guard.condition ≠ booleanRelationCondition false left right := by
  intro equality
  by_cases truth : right = .const ``Bool.true []
  · subst right
    exact guard.not_boolean_condition left equality
  · have accepted := guardOperands_condition guard.value
    change guardOperands? guard.condition = some guard.value at accepted
    rw [equality, booleanRelationEqual_not_guard left right truth] at accepted
    contradiction

theorem propositionGuard_not_boolean_unequal (guard : PropositionGuard) (left right : Lean.Expr) :
    guard.condition ≠ booleanRelationCondition true left right := by
  intro equality
  have accepted := guardOperands_condition guard.value
  change guardOperands? guard.condition = some guard.value at accepted
  rw [equality, booleanRelationUnequal_not_guard left right] at accepted
  contradiction

end LeanExe.Extract.Core
