import LeanExe.Source.ScalarBooleanJoined
import LeanExe.Extract.ScalarBooleanNegated

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

@[simp] theorem booleanJoined_not_local (value : BooleanJoined) :
    booleanLocalOperands? value.expr = none := by
  cases found : booleanLocalOperands? value.expr with
  | none => rfl
  | some expression => exact False.elim (value.extended expression (booleanLocalOperands_sound found))

def booleanJoined? (source : Lean.Expr) : Option BooleanJoined :=
  if absent : booleanLocalOperands? source = none then
    match source with
    | .app (.app (.const ``Bool.and []) left) right =>
        some ⟨.conjunction, left, right, booleanLocal_excluded absent⟩
    | .app (.app (.const ``Bool.or []) left) right =>
        some ⟨.disjunction, left, right, booleanLocal_excluded absent⟩
    | _ => none
  else none

@[simp] theorem booleanJoined_accepts (value : BooleanJoined) :
    booleanJoined? value.expr = some value := by
  have absent := booleanJoined_not_local value
  rcases value with ⟨operation, left, right, extended⟩
  cases operation <;>
    simp only [BooleanJoined.expr, Junction.booleanExpr] at absent ⊢
  all_goals simp [booleanJoined?, absent]

theorem booleanJoined_sound {source : Lean.Expr} {value : BooleanJoined}
    (parsed : booleanJoined? source = some value) : source = value.expr := by
  unfold booleanJoined? at parsed
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  all_goals cases parsed; rfl

@[simp] theorem booleanJoined_not_helper (value : BooleanJoined) (booleanInput : Bool) :
    booleanHelper? booleanInput value.expr = none := by
  unfold booleanHelper?
  rw [dite_eq_left (booleanJoined_not_local value)]
  rcases value with ⟨operation, left, right, extended⟩
  cases operation <;> rfl

@[simp] theorem booleanJoined_not_wrapped (value : BooleanJoined) :
    booleanWrapped? value.expr = none := by
  unfold booleanWrapped?
  rw [dite_eq_left (booleanJoined_not_local value)]
  rcases value with ⟨operation, left, right, extended⟩
  cases operation <;> rfl

@[simp] theorem booleanJoined_not_negated (value : BooleanJoined) :
    booleanNegated? value.expr = none := by
  unfold booleanNegated?
  rw [dite_eq_left (booleanJoined_not_local value)]
  rcases value with ⟨operation, left, right, extended⟩
  cases operation <;> rfl

theorem booleanJoined_sizes {source : Lean.Expr} {value : BooleanJoined}
    (parsed : booleanJoined? source = some value) :
    sizeOf value.left < sizeOf source ∧ sizeOf value.right < sizeOf source := by
  rw [booleanJoined_sound parsed]
  exact value.children_size

end LeanExe.Extract.Core
