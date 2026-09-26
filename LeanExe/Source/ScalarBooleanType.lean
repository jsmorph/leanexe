import Lean

namespace LeanExe.Source.Scalar

/-- Boolean action annotations retain every Id layer introduced by elaboration. -/
inductive BooleanType where
  | boolean
  | identity (inner : BooleanType)
  deriving DecidableEq, Repr

def BooleanType.expr : BooleanType → Lean.Expr
  | .boolean => .const ``Bool []
  | .identity inner => .app (.const ``Id [.zero]) inner.expr

end LeanExe.Source.Scalar
