import LeanExe.Source.ScalarBooleanLocal

namespace LeanExe.Source.Scalar

/-- A standard Boolean wrapper around a recursively supported expression. -/
structure BooleanWrapped where
  wrapper : BooleanWrapper
  body : Lean.Expr
  extended : ∀ expression : BooleanLocal, wrapper.expr body ≠ expression.expr
  deriving Repr

namespace BooleanWrapped

def expr (value : BooleanWrapped) : Lean.Expr := value.wrapper.expr value.body

theorem body_size (value : BooleanWrapped) : sizeOf value.body < sizeOf value.expr :=
  value.wrapper.body_size value.body

end BooleanWrapped
end LeanExe.Source.Scalar
