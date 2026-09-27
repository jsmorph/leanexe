import Lean

namespace LeanExe.Source.Scalar

/-- Preserve an exact standard Id layer around a let's underlying type. -/
def idLetExpr (name : Lean.Name) (type value body : Lean.Expr) (nondep : Bool) : Lean.Expr :=
  .letE name (.app (.const ``Id [.zero]) type) value body nondep

theorem idLetExpr_size (name : Lean.Name) (type value body : Lean.Expr) (nondep : Bool) :
    sizeOf (Lean.Expr.letE name type value body nondep) < sizeOf (idLetExpr name type value body nondep) := by
  simp [idLetExpr]
  omega

end LeanExe.Source.Scalar
