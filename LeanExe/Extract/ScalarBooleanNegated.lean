import LeanExe.Source.ScalarBooleanNegated
import LeanExe.Extract.ScalarBooleanWrapped

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

@[simp] theorem booleanNegated_not_local (value : BooleanNegated) :
    booleanLocalOperands? value.expr = none := by
  cases found : booleanLocalOperands? value.expr with
  | none => rfl
  | some expression => exact False.elim (value.extended expression (booleanLocalOperands_sound found))

def booleanNegated? (source : Lean.Expr) : Option BooleanNegated :=
  if absent : booleanLocalOperands? source = none then
    match source with
    | .app (.const ``Bool.not []) body => some ⟨body, booleanLocal_excluded absent⟩
    | _ => none
  else none

@[simp] theorem booleanNegated_accepts (value : BooleanNegated) :
    booleanNegated? value.expr = some value := by
  have absent := booleanNegated_not_local value
  rcases value with ⟨body, extended⟩
  simp only [BooleanNegated.expr] at absent ⊢
  simp [booleanNegated?, absent]

theorem booleanNegated_sound {source : Lean.Expr} {value : BooleanNegated}
    (parsed : booleanNegated? source = some value) : source = value.expr := by
  unfold booleanNegated? at parsed
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  cases parsed
  rfl

@[simp] theorem booleanNegated_not_helper (value : BooleanNegated) (booleanInput : Bool) :
    booleanHelper? booleanInput value.expr = none := by
  unfold booleanHelper?
  rw [dite_eq_left (booleanNegated_not_local value)]
  rfl

@[simp] theorem booleanNegated_not_wrapped (value : BooleanNegated) :
    booleanWrapped? value.expr = none := by
  unfold booleanWrapped?
  rw [dite_eq_left (booleanNegated_not_local value)]
  rfl

theorem booleanNegated_size {source : Lean.Expr} {value : BooleanNegated}
    (parsed : booleanNegated? source = some value) : sizeOf value.body < sizeOf source := by
  rw [booleanNegated_sound parsed]
  exact value.body_size

end LeanExe.Extract.Core
