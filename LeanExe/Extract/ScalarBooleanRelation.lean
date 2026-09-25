import LeanExe.Source.ScalarBooleanLocal
import LeanExe.Extract.ScalarGuardSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

theorem booleanRelationEqual_not_comparison (left right : Lean.Expr)
    (nontrue : right ≠ .const ``Bool.true []) :
    comparisonOperands? (booleanRelationCondition false left right) = none := by
  rw [booleanRelationCondition, comparisonOperands?] <;> simp_all

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

end LeanExe.Extract.Core
