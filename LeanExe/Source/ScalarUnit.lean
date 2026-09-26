import Lean

namespace LeanExe.Source.Scalar

/-- Equivalent concrete unit spellings retained by elaborated do continuations. -/
inductive UnitSyntax where
  | unit | punit
  deriving DecidableEq, Repr

abbrev UnitSyntax.type : UnitSyntax → Lean.Expr
  | .unit => .const ``Unit []
  | .punit => .const ``PUnit [.succ .zero]

abbrev UnitSyntax.value : UnitSyntax → Lean.Expr
  | .unit => .const ``Unit.unit []
  | .punit => .const ``PUnit.unit [.succ .zero]

end LeanExe.Source.Scalar
