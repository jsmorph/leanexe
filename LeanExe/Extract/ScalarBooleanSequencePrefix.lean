import LeanExe.Extract.ScalarBooleanWordRange
import LeanExe.Source.ScalarBooleanSequencePrefix

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Boolean prefixes require an exact scalar result type and standard Id instance. -/
def booleanSequencePrefix? (boolean : Bool) (source : Lean.Expr) : Option (BooleanSequencePrefix boolean) :=
  match source with
  | .letE name type value body nondep => do
      let input ← booleanType? type
      pure ⟨name, input, .letE nondep, value, body⟩
  | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))) input) output) value)
      (.lam name domain body binder) =>
      match boolean with
      | false => do
          let (input, output) ← booleanWordRangeBindTypes? input domain output
          pure ⟨name, input, .wordBind binder output, value, body⟩
      | true => do
          let (input, output) ← booleanRangeFlagBindTypes? input domain output
          pure ⟨name, input, .booleanBind binder output, value, body⟩
  | _ => none

@[simp] theorem booleanSequencePrefix_accepts (shape : BooleanSequencePrefix boolean) :
    booleanSequencePrefix? boolean shape.expr = some shape := by
  cases shape with
  | mk name input form value body =>
    cases form <;> simp [BooleanSequencePrefix.expr, BooleanWordRange.bind, BooleanRange.bindBoolean,
      BooleanBindingForm.expr, booleanSequencePrefix?]

theorem booleanSequencePrefix_sound {boolean : Bool} {source : Lean.Expr}
    {shape : BooleanSequencePrefix boolean}
    (parsed : booleanSequencePrefix? boolean source = some shape) : source = shape.expr := by
  unfold booleanSequencePrefix? at parsed
  split at parsed
  · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨input, typed, rfl⟩ := parsed
    simp only [BooleanSequencePrefix.expr, booleanType_sound typed]
  · split at parsed
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨⟨input, output⟩, typed, rfl⟩ := parsed
      obtain ⟨rfl, rfl, rfl⟩ := booleanWordRangeBindTypes_sound typed
      rfl
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨⟨input, output⟩, typed, rfl⟩ := parsed
      obtain ⟨rfl, rfl, rfl⟩ := booleanRangeFlagBindTypes_sound typed
      rfl
  · contradiction

theorem booleanSequencePrefix_body_size {boolean : Bool} {source : Lean.Expr}
    {shape : BooleanSequencePrefix boolean}
    (parsed : booleanSequencePrefix? boolean source = some shape) : sizeOf shape.body < sizeOf source := by
  rw [booleanSequencePrefix_sound parsed]
  exact shape.body_size

@[simp] theorem booleanSequencePrefix_word_let (boolean : Bool) (input : ResultType)
    (name : Lean.Name) (value body : Lean.Expr) (nondep : Bool) :
    booleanSequencePrefix? boolean (.letE name input.expr value body nondep) = none := by
  simp [booleanSequencePrefix?, booleanType_scalar]

@[simp] theorem booleanSequencePrefix_word_bind (input output : ResultType)
    (name : Lean.Name) (binder : Lean.BinderInfo) (value body : Lean.Expr) :
    booleanSequencePrefix? false (Identity.bind name binder value body input output) = none := by
  simp [Identity.bind, booleanSequencePrefix?, booleanWordRangeBindTypes?, booleanType_scalar]

@[simp] theorem booleanSequencePrefix_word_boolean_bind (input : ResultType) (output : BooleanType)
    (name : Lean.Name) (binder : Lean.BinderInfo) (value body : Lean.Expr) :
    booleanSequencePrefix? true (BooleanRange.bind name binder input output value body) = none := by
  simp [BooleanRange.bind, BooleanBindingForm.expr, booleanSequencePrefix?, booleanRangeFlagBindTypes?, booleanType_scalar]

end LeanExe.Extract.Core
