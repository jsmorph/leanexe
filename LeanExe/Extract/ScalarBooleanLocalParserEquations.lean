import LeanExe.Extract.ScalarBooleanLocalParser
import LeanExe.Extract.ScalarBooleanRelation

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

@[simp] theorem booleanLocalOperands_dependentChoice (shape : BooleanProofBranch)
    (unequal : Bool) (left right yes no : Lean.Expr) :
    booleanLocalOperands? (shape.expr (booleanRelationCondition unequal left right)
      (booleanRelationEvidence unequal left right) yes no) = (do
      let a ← booleanLocalOperands? left
      let b ← booleanLocalOperands? right
      let t ← booleanLocalOperands? yes
      let e ← booleanLocalOperands? no
      pure (.dependentChoice 0 shape unequal a b t e)) := by
  cases shape
  cases unequal <;> simp only [BooleanProofBranch.expr, booleanRelationCondition]
  all_goals rw [booleanLocalOperands?.eq_def]
  all_goals simp [booleanRelationCondition]
  all_goals rw [booleanProofBodies_accepts]

@[simp] theorem booleanLocalOperands_dependentProposition (shape : BooleanProofBranch)
    (guard : PropositionGuard) (yes no : Lean.Expr) :
    booleanLocalOperands? (shape.expr guard.condition guard.evidence yes no) = (do
      let t ← booleanLocalOperands? yes
      let e ← booleanLocalOperands? no
      pure (.dependentProposition 0 shape guard t e)) := by
  rw [BooleanProofBranch.expr, booleanLocalOperands?]
  · rw [booleanProofBodies_accepts, propositionGuard_accepts]
    rfl
  · intro left right equality
    exact propositionGuard_not_boolean_equal guard left right equality
  · intro left right equality
    exact propositionGuard_not_boolean_unequal guard left right equality

end LeanExe.Extract.Core
