import LeanExe.Source.ScalarBooleanLocal

namespace LeanExe.Source.Scalar

/-- Boolean negation whose operand needs recursive scalar conversion. -/
structure BooleanNegated where
  body : Lean.Expr
  extended : ∀ expression : BooleanLocal, Lean.Expr.app (.const ``Bool.not []) body ≠ expression.expr
  deriving Repr

namespace BooleanNegated

def expr (value : BooleanNegated) : Lean.Expr := .app (.const ``Bool.not []) value.body

theorem body_size (value : BooleanNegated) : sizeOf value.body < sizeOf value.expr := by
  simp [expr] <;> omega

end BooleanNegated
end LeanExe.Source.Scalar
