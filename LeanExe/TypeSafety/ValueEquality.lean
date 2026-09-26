import LeanExe.TypeSafety.Core

/-!
# Structural comparison of finite raw values

This mathematical comparison is total on the existing untyped `Value` syntax,
including malformed values. It checks every tag and field, not allocation identity
or user-selected equality instances. Recursion follows the finite value tree and
its finite field lists, independently of nominal declaration graphs.

The exact correctness laws below specify the raw algorithm only. This module adds
no expression primitive, equality-admission judgment, or source typing rule.
In particular, comparing recursive values here does not admit recursive source
types into the documented structural-equality domain.
-/

namespace LeanExe.TypeSafety

mutual
def valueEq : Value → Value → Bool
  | .unit, .unit => true
  | .bool left, .bool right => decide (left = right)
  | .nat left, .nat right => decide (left = right)
  | .word leftWidth left, .word rightWidth right =>
      decide (leftWidth = rightWidth) && decide (left = right)
  | .pair leftFirst leftSecond, .pair rightFirst rightSecond =>
      valueEq leftFirst rightFirst && valueEq leftSecond rightSecond
  | .inl left, .inl right => valueEq left right
  | .inr left, .inr right => valueEq left right
  | .array left, .array right => valuesEq left right
  | .data leftData leftCtor leftFields, .data rightData rightCtor rightFields =>
      decide (leftData = rightData) &&
        (decide (leftCtor = rightCtor) && valuesEq leftFields rightFields)
  | _, _ => false

def valuesEq : List Value → List Value → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest => valueEq left right && valuesEq leftRest rightRest
  | _, _ => false
end

mutual
theorem valueEq_sound (same : valueEq left right = true) : left = right := by
  cases left <;> cases right <;>
    simp only [valueEq, Bool.and_eq_true, decide_eq_true_eq] at same
  all_goals try contradiction
  · rfl
  · cases same; rfl
  · cases same; rfl
  · obtain ⟨width, value⟩ := same; cases width; cases value; rfl
  · obtain ⟨first, second⟩ := same
    rw [valueEq_sound first, valueEq_sound second]
  · rw [valueEq_sound same]
  · rw [valueEq_sound same]
  · rw [valuesEq_sound same]
  · obtain ⟨dataId, constructor, fields⟩ := same
    cases dataId; cases constructor
    rw [valuesEq_sound fields]

theorem valuesEq_sound (same : valuesEq left right = true) : left = right := by
  cases left <;> cases right <;> simp only [valuesEq, Bool.and_eq_true] at same
  all_goals try contradiction
  · rfl
  · obtain ⟨head, tail⟩ := same
    rw [valueEq_sound head, valuesEq_sound tail]
end

mutual
theorem valueEq_refl (value : Value) : valueEq value value = true := by
  cases value <;> simp only [valueEq, decide_true, Bool.true_and]
  · exact Bool.and_eq_true_iff.mpr ⟨valueEq_refl _, valueEq_refl _⟩
  · exact valueEq_refl _
  · exact valueEq_refl _
  · exact valuesEq_refl _
  · exact valuesEq_refl _

theorem valuesEq_refl (values : List Value) : valuesEq values values = true := by
  cases values with
  | nil => rfl
  | cons head tail => exact Bool.and_eq_true_iff.mpr ⟨valueEq_refl head, valuesEq_refl tail⟩
end

/-- Success means equality of the complete raw value, including all shape and nominal tags. -/
theorem valueEq_eq_true_iff : valueEq left right = true ↔ left = right := by
  constructor
  · exact valueEq_sound
  · intro same
    cases same
    exact valueEq_refl _

/-- Lists must have exactly the same length and the same values in order. -/
theorem valuesEq_eq_true_iff : valuesEq left right = true ↔ left = right := by
  constructor
  · exact valuesEq_sound
  · intro same
    cases same
    exact valuesEq_refl _

theorem valueEq_eq_false_iff : valueEq left right = false ↔ left ≠ right := by
  constructor
  · intro different same
    cases same
    rw [valueEq_refl] at different
    cases different
  · intro different
    cases compared : valueEq left right with
    | false => rfl
    | true => exact False.elim (different (valueEq_sound compared))

theorem valuesEq_eq_false_iff : valuesEq left right = false ↔ left ≠ right := by
  constructor
  · intro different same
    cases same
    rw [valuesEq_refl] at different
    cases different
  · intro different
    cases compared : valuesEq left right with
    | false => rfl
    | true => exact False.elim (different (valuesEq_sound compared))

theorem valueEq_symm : valueEq left right = valueEq right left := by
  cases forward : valueEq left right <;> cases backward : valueEq right left
  · rfl
  · have same := valueEq_sound backward
    cases same
    rw [valueEq_refl] at forward
    cases forward
  · have same := valueEq_sound forward
    cases same
    rw [valueEq_refl] at backward
    cases backward
  · rfl

theorem valuesEq_symm : valuesEq left right = valuesEq right left := by
  cases forward : valuesEq left right <;> cases backward : valuesEq right left
  · rfl
  · have same := valuesEq_sound backward
    cases same
    rw [valuesEq_refl] at forward
    cases forward
  · have same := valuesEq_sound forward
    cases same
    rw [valuesEq_refl] at backward
    cases backward
  · rfl

theorem valueEq_pair : valueEq (.pair leftFirst leftSecond) (.pair rightFirst rightSecond) =
    (valueEq leftFirst rightFirst && valueEq leftSecond rightSecond) := rfl

theorem valueEq_word : valueEq (.word leftWidth left) (.word rightWidth right) =
    (decide (leftWidth = rightWidth) && decide (left = right)) := rfl

theorem valueEq_sum_tags : valueEq (.inl left) (.inr right) = false := rfl

theorem valueEq_array : valueEq (.array left) (.array right) = valuesEq left right := rfl

theorem valueEq_data :
    valueEq (.data leftData leftCtor leftFields) (.data rightData rightCtor rightFields) =
      (decide (leftData = rightData) &&
        (decide (leftCtor = rightCtor) && valuesEq leftFields rightFields)) := rfl

theorem valuesEq_nil_left : valuesEq [] (head :: tail) = false := rfl

theorem valuesEq_nil_right : valuesEq (head :: tail) [] = false := rfl

theorem valuesEq_cons : valuesEq (left :: leftRest) (right :: rightRest) =
    (valueEq left right && valuesEq leftRest rightRest) := rfl

theorem valuesEq_length (same : valuesEq left right = true) : left.length = right.length :=
  congrArg List.length (valuesEq_sound same)

end LeanExe.TypeSafety
