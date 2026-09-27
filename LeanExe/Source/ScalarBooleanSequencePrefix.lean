import LeanExe.Source.ScalarBooleanWordRange

namespace LeanExe.Source.Scalar

/-- Exact let/bind syntax for a Boolean value followed by a scalar computation. -/
inductive BooleanSequenceForm : Bool → Type where
  | letE (nondep : Bool) : BooleanSequenceForm boolean
  | wordBind (binder : Lean.BinderInfo) (output : ResultType) : BooleanSequenceForm false
  | booleanBind (binder : Lean.BinderInfo) (output : BooleanType) : BooleanSequenceForm true

structure BooleanSequencePrefix (boolean : Bool) where
  name : Lean.Name
  input : BooleanType
  form : BooleanSequenceForm boolean
  value : Lean.Expr
  body : Lean.Expr

namespace BooleanSequencePrefix

def expr (shape : BooleanSequencePrefix boolean) : Lean.Expr :=
  match shape.form with
  | .letE nondep => .letE shape.name shape.input.expr shape.value shape.body nondep
  | .wordBind binder output => BooleanWordRange.bind shape.name binder shape.input output shape.value shape.body
  | .booleanBind binder output => BooleanRange.bindBoolean shape.name binder shape.input output shape.value shape.body

theorem body_size (shape : BooleanSequencePrefix boolean) : sizeOf shape.body < sizeOf shape.expr := by
  cases shape with
  | mk name input form value body =>
    cases form <;> simp [expr, BooleanWordRange.bind, BooleanRange.bindBoolean, BooleanBindingForm.expr] <;> omega

end BooleanSequencePrefix
end LeanExe.Source.Scalar
