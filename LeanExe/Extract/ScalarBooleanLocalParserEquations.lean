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
  cases unequal <;> simp only [BooleanProofBranch.expr, booleanRelationCondition,
    Bool.false_eq_true, ite_false, ite_true]
  all_goals first
    | rw [booleanLocalOperands?.eq_10]
    | rw [booleanLocalOperands?.eq_11]
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

@[simp] theorem booleanLocalOperands_binding (name : Lean.Name) (nondep : BooleanBindingForm)
    (type : BooleanType) (value body : Lean.Expr) :
    booleanLocalOperands? (nondep.expr name type.expr value body) = (do
      let v ← booleanLocalOperands? value
      let b ← booleanLocalOperands? body
      pure (.binding 0 name nondep v b type)) := by
  cases nondep <;> rw [BooleanBindingForm.expr, booleanLocalOperands?, scalarResultType_boolean, booleanType_accepts] <;> rfl

@[simp] theorem booleanLocalOperands_wordBinding (name : Lean.Name) (nondep : BooleanBindingForm)
    (type : ResultType) (value body : Lean.Expr) :
    booleanLocalOperands? (nondep.expr name type.expr value body) = (do
      let b ← booleanLocalOperands? body
      pure (.wordBinding 0 name nondep value b type)) := by
  cases nondep <;> rw [BooleanBindingForm.expr, booleanLocalOperands?, scalarResultType_accepts]

@[simp] theorem booleanLocalOperands_wrapped (wrapper : BooleanWrapper) (body : Lean.Expr) :
    booleanLocalOperands? (wrapper.expr body) =
      (booleanLocalOperands? body).map (fun value => .wrapped 0 wrapper value) := by
  cases wrapper <;> simp [BooleanWrapper.expr, BooleanIdentity.run, BooleanIdentity.pure,
    booleanLocalOperands?]

end LeanExe.Extract.Core
