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

@[simp] theorem booleanLocalOperands_binding (name : Lean.Name) (form : BooleanBindingForm)
    (type : BooleanType) (value body : Lean.Expr) :
    booleanLocalOperands? (form.expr name type.expr value body) = (do
      let v ← booleanLocalOperands? value
      let b ← booleanLocalOperands? body
      pure (.binding 0 name form v b type)) := by
  cases form with
  | letE nondep =>
      rw [BooleanBindingForm.expr, booleanLocalOperands?, booleanFunctionApplication_booleanLet,
        scalarResultType_boolean, booleanType_accepts]
      rfl
  | application binder =>
      rw [BooleanBindingForm.expr, booleanLocalOperands?, scalarResultType_boolean, booleanType_accepts]
      rfl
  | namedApplication shape =>
      rw [BooleanBindingForm.expr, BooleanFunctionBinding.expr, booleanLocalOperands?]
      have accepted := booleanFunctionApplication_accepts (⟨shape, name, type.expr, value, body⟩ : BooleanFunctionApplication)
      split
      · rename_i application found
        have same : application = (⟨shape, name, type.expr, value, body⟩ : BooleanFunctionApplication) :=
          Option.some.inj (found.symm.trans accepted)
        subst application
        simp [scalarResultType_boolean, booleanType_accepts]
      · rename_i rejected
        have impossible := rejected.symm.trans accepted
        cases impossible

@[simp] theorem booleanLocalOperands_wordBinding (name : Lean.Name) (form : BooleanBindingForm)
    (type : ResultType) (value body : Lean.Expr) :
    booleanLocalOperands? (form.expr name type.expr value body) = (do
      let b ← booleanLocalOperands? body
      pure (.wordBinding 0 name form value b type)) := by
  cases form with
  | letE nondep =>
      rw [BooleanBindingForm.expr, booleanLocalOperands?, booleanFunctionApplication_wordLet,
        scalarResultType_accepts]
  | application binder =>
      rw [BooleanBindingForm.expr, booleanLocalOperands?, scalarResultType_accepts]
  | namedApplication shape =>
      rw [BooleanBindingForm.expr, BooleanFunctionBinding.expr, booleanLocalOperands?]
      have accepted := booleanFunctionApplication_accepts (⟨shape, name, type.expr, value, body⟩ : BooleanFunctionApplication)
      split
      · rename_i application found
        have same : application = (⟨shape, name, type.expr, value, body⟩ : BooleanFunctionApplication) :=
          Option.some.inj (found.symm.trans accepted)
        subst application
        simp [scalarResultType_accepts]
      · rename_i rejected
        have impossible := rejected.symm.trans accepted
        cases impossible

@[simp] theorem booleanLocalOperands_wrapped (wrapper : BooleanWrapper) (body : Lean.Expr) :
    booleanLocalOperands? (wrapper.expr body) =
      (booleanLocalOperands? body).map (fun value => .wrapped 0 wrapper value) := by
  cases wrapper <;> simp [BooleanWrapper.expr, BooleanIdentity.run, BooleanIdentity.pure,
    booleanLocalOperands?]

end LeanExe.Extract.Core
