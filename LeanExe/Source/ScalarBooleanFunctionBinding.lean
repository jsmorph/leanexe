import LeanExe.Source.ScalarBooleanWrapper
import LeanExe.Source.ExprProofBinder

namespace LeanExe.Source.Scalar

/-- A local Boolean call retains standard identity wrappers around its result. -/
inductive BooleanApplicationTail where
  | direct
  | wrapped (wrapper : BooleanWrapper) (tail : BooleanApplicationTail)
  deriving Repr

namespace BooleanApplicationTail

def expr : BooleanApplicationTail → Lean.Expr → Lean.Expr
  | .direct, argument => .app (.bvar 0) (ExprProofBinder.lift 0 argument)
  | .wrapped wrapper tail, argument => wrapper.expr (tail.expr argument)

theorem call_size (tail : BooleanApplicationTail) (argument : Lean.Expr) :
    sizeOf (BooleanApplicationTail.direct.expr argument) ≤ sizeOf (tail.expr argument) := by
  induction tail with
  | direct => exact Nat.le_refl _
  | wrapped wrapper tail ih =>
    exact Nat.le_trans ih (Nat.le_of_lt (wrapper.body_size (tail.expr argument)))

end BooleanApplicationTail

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

/-- Apply the checked helper and preserve the syntax around the call result. -/
def appliedExpr (shape : BooleanFunctionBinding) (tail : BooleanApplicationTail)
    (parameterName : Lean.Name) (input argument body : Lean.Expr) : Lean.Expr :=
  .letE shape.functionName
    (.forallE shape.typeName input shape.result.expr shape.typeInfo)
    (.lam parameterName input body shape.valueInfo)
    (tail.expr argument) shape.nondep

@[simp] theorem appliedExpr_direct (shape : BooleanFunctionBinding) (parameterName : Lean.Name)
    (input argument body : Lean.Expr) :
    shape.appliedExpr .direct parameterName input argument body =
      shape.expr parameterName input argument body := rfl

theorem applied_binding_size (shape : BooleanFunctionBinding) (tail : BooleanApplicationTail)
    (parameterName : Lean.Name) (input argument body : Lean.Expr) :
    sizeOf (.letE parameterName input argument body false : Lean.Expr) ≤
      sizeOf (shape.appliedExpr tail parameterName input argument body) := by
  have bound := shape.binding_size parameterName input argument body
  have callBound := tail.call_size argument
  simp only [expr, appliedExpr, BooleanApplicationTail.expr] at *
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
  tail : BooleanApplicationTail := .direct
  deriving Repr

abbrev BooleanFunctionApplication.expr (value : BooleanFunctionApplication) : Lean.Expr :=
  value.shape.appliedExpr value.tail value.parameterName value.input value.argument value.body

theorem BooleanFunctionApplication.argument_size (value : BooleanFunctionApplication) :
    sizeOf value.argument < sizeOf value.expr := by
  have bound := value.shape.applied_binding_size value.tail value.parameterName value.input value.argument value.body
  simp_all [BooleanFunctionApplication.expr]
  omega

theorem BooleanFunctionApplication.body_size (value : BooleanFunctionApplication) :
    sizeOf value.body < sizeOf value.expr := by
  have bound := value.shape.applied_binding_size value.tail value.parameterName value.input value.argument value.body
  simp_all [BooleanFunctionApplication.expr]
  omega

end LeanExe.Source.Scalar
