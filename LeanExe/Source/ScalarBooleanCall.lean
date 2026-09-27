import LeanExe.Source.ScalarBooleanFunctionBinding
import LeanExe.Source.ScalarBooleanWrapper
import LeanExe.Source.ScalarBooleanLet

namespace LeanExe.Source.Scalar

/-- Local calls preserve word/Boolean inputs, standard Id sequencing and result wrappers. -/
inductive BooleanCall : Bool → Type where
  | direct : BooleanCall boolean
  | wrapped (wrapper : BooleanWrapper) (inner : BooleanCall boolean) : BooleanCall boolean
  | savedResult (name : Lean.Name) (type : BooleanType) (nondep : Bool)
      (inner : BooleanCall boolean) : BooleanCall boolean
  | forwardWord (input : ResultType) (output : BooleanType)
      (name : Lean.Name) (binder : Lean.BinderInfo) : BooleanCall false
  | forwardBoolean (input output : BooleanType)
      (name : Lean.Name) (binder : Lean.BinderInfo) : BooleanCall true
  deriving Repr

def BooleanCall.expr : BooleanCall boolean → Lean.Expr → Lean.Expr
  | .direct, argument => .app (.bvar 0) (LeanExe.Source.ExprProofBinder.lift 0 argument)
  | .wrapped wrapper inner, argument => wrapper.expr (inner.expr argument)
  | .savedResult name type nondep inner, argument =>
      .letE name type.expr (inner.expr argument) (.bvar 0) nondep
  | .forwardWord input output name binder, argument =>
      (BooleanBindingForm.monadic binder output).expr name input.expr
        (LeanExe.Source.ExprProofBinder.lift 0 argument) (.app (.bvar 1) (.bvar 0))
  | .forwardBoolean input output name binder, argument =>
      (BooleanBindingForm.monadic binder output).expr name input.expr
        (LeanExe.Source.ExprProofBinder.lift 0 argument) (.app (.bvar 1) (.bvar 0))

def BooleanFunctionBinding.callExpr (shape : BooleanFunctionBinding) (call : BooleanCall boolean)
    (parameterName : Lean.Name) (input argument body : Lean.Expr) : Lean.Expr :=
  .letE shape.functionName
    (.forallE shape.typeName input shape.result.expr shape.typeInfo)
    (.lam parameterName input body shape.valueInfo)
    (call.expr argument) shape.nondep

@[simp] theorem BooleanFunctionBinding.directCall (boolean : Bool) (shape : BooleanFunctionBinding)
    (parameterName : Lean.Name) (input argument body : Lean.Expr) :
    shape.callExpr (BooleanCall.direct (boolean := boolean)) parameterName input argument body =
      shape.expr parameterName input argument body := rfl

end LeanExe.Source.Scalar
