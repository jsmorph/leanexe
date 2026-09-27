import LeanExe.Source.ScalarBooleanFunctionBinding
import LeanExe.Source.ScalarBooleanWrapper

namespace LeanExe.Source.Scalar

/-- A local call retains each standard Boolean wrapper around its result. -/
inductive BooleanCall where
  | direct
  | wrapped (wrapper : BooleanWrapper) (inner : BooleanCall)
  deriving Repr

def BooleanCall.expr : BooleanCall → Lean.Expr → Lean.Expr
  | .direct, argument => .app (.bvar 0) (LeanExe.Source.ExprProofBinder.lift 0 argument)
  | .wrapped wrapper inner, argument => wrapper.expr (inner.expr argument)

def BooleanFunctionBinding.callExpr (shape : BooleanFunctionBinding) (call : BooleanCall)
    (parameterName : Lean.Name) (input argument body : Lean.Expr) : Lean.Expr :=
  .letE shape.functionName
    (.forallE shape.typeName input shape.result.expr shape.typeInfo)
    (.lam parameterName input body shape.valueInfo)
    (call.expr argument) shape.nondep

@[simp] theorem BooleanFunctionBinding.directCall (shape : BooleanFunctionBinding)
    (parameterName : Lean.Name) (input argument body : Lean.Expr) :
    shape.callExpr .direct parameterName input argument body =
      shape.expr parameterName input argument body := rfl

end LeanExe.Source.Scalar
