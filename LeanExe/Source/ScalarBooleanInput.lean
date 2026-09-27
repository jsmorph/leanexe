import LeanExe.Source.ScalarBooleanType

namespace LeanExe.Source.Scalar

/-- Matching Bool-input annotations on a local helper declaration. The inner
source derivation checks its result annotation, body and uses. -/
def booleanInputExpr (input : BooleanType) (result : Lean.Expr)
    (name typeName paramName : Lean.Name) (typeBi paramBi : Lean.BinderInfo)
    (value body : Lean.Expr) (nondep : Bool) : Lean.Expr :=
  .letE name (.forallE typeName input.expr result typeBi)
    (.lam paramName input.expr value paramBi) body nondep

end LeanExe.Source.Scalar
