import LeanExe.Source.ScalarBooleanType
import LeanExe.Source.ScalarDo

namespace LeanExe.Source.Scalar

/-- A predicate declaration with matching arrow and lambda input annotations. -/
def predicateInputExpr (input : ResultType) (result : BooleanType)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (value body : Lean.Expr) (nondep : Bool) : Lean.Expr :=
  .letE name (.forallE typeName input.expr result.expr typeBi)
    (.lam paramName input.expr value paramBi) body nondep

end LeanExe.Source.Scalar
