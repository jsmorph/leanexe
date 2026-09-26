import LeanExe.Source.ScalarBooleanType
import LeanExe.Source.ExprProofBinder

namespace LeanExe.Source.Scalar

/-- Exact annotations of a named Boolean helper applied in its binding body. -/
structure BooleanFunctionBinding where
  functionName : Lean.Name
  typeName : Lean.Name
  typeInfo : Lean.BinderInfo
  valueInfo : Lean.BinderInfo
  result : BooleanType
  nondep : Bool
  deriving Repr

namespace BooleanFunctionBinding

def expr (shape : BooleanFunctionBinding) (parameterName : Lean.Name)
    (input argument body : Lean.Expr) : Lean.Expr :=
  .letE shape.functionName
    (.forallE shape.typeName input shape.result.expr shape.typeInfo)
    (.lam parameterName input body shape.valueInfo)
    (.app (.bvar 0) (ExprProofBinder.lift 0 argument)) shape.nondep

/-- The argument's canonical lexical binding fits inside the original helper. -/
theorem binding_size (shape : BooleanFunctionBinding) (parameterName : Lean.Name)
    (input argument body : Lean.Expr) :
    sizeOf (.letE parameterName input argument body false : Lean.Expr) ≤
      sizeOf (shape.expr parameterName input argument body) := by
  have bound := ExprProofBinder.lift_size argument 0
  simp only [expr]
  simp_all
  omega

end BooleanFunctionBinding

/-- Recognized syntax before checking the argument's word or Boolean type. -/
structure BooleanFunctionApplication where
  shape : BooleanFunctionBinding
  parameterName : Lean.Name
  input : Lean.Expr
  argument : Lean.Expr
  body : Lean.Expr
  deriving Repr

abbrev BooleanFunctionApplication.expr (value : BooleanFunctionApplication) : Lean.Expr :=
  value.shape.expr value.parameterName value.input value.argument value.body

theorem BooleanFunctionApplication.argument_size (value : BooleanFunctionApplication) :
    sizeOf value.argument < sizeOf value.expr := by
  have bound := value.shape.binding_size value.parameterName value.input value.argument value.body
  simp_all [BooleanFunctionApplication.expr]
  omega

theorem BooleanFunctionApplication.body_size (value : BooleanFunctionApplication) :
    sizeOf value.body < sizeOf value.expr := by
  have bound := value.shape.binding_size value.parameterName value.input value.argument value.body
  simp_all [BooleanFunctionApplication.expr]
  omega

end LeanExe.Source.Scalar
