import LeanExe.Source.ExprProofBinder

namespace LeanExe.Source.Scalar

/-- Exact proof-lambda names and binder annotations for a dependent Bool result. -/
structure BooleanProofBranch where
  trueName : Lean.Name
  falseName : Lean.Name
  trueInfo : Lean.BinderInfo
  falseInfo : Lean.BinderInfo
  deriving Repr

namespace BooleanProofBranch

def expr (shape : BooleanProofBranch) (condition evidence yes no : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) (.const ``Bool []))
    condition) evidence)
    (.lam shape.trueName condition (ExprProofBinder.lift 0 yes) shape.trueInfo))
    (.lam shape.falseName (.app (.const ``Not []) condition) (ExprProofBinder.lift 0 no) shape.falseInfo)

theorem condition_size (shape : BooleanProofBranch) (condition evidence yes no : Lean.Expr) :
    sizeOf condition < sizeOf (shape.expr condition evidence yes no) := by
  simp [expr]
  omega

theorem yes_size (shape : BooleanProofBranch) (condition evidence yes no : Lean.Expr) :
    sizeOf yes < sizeOf (shape.expr condition evidence yes no) := by
  have bound := ExprProofBinder.lift_size yes 0
  simp only [expr]
  simp_all
  omega

theorem no_size (shape : BooleanProofBranch) (condition evidence yes no : Lean.Expr) :
    sizeOf no < sizeOf (shape.expr condition evidence yes no) := by
  have bound := ExprProofBinder.lift_size no 0
  simp only [expr]
  simp_all
  omega

end BooleanProofBranch
end LeanExe.Source.Scalar
