import LeanExe.Source.ScalarBooleanLocal

namespace LeanExe.Source.Scalar

/-- A Boolean junction with recursively supported operands. -/
structure BooleanJoined where
  operation : Junction
  left : Lean.Expr
  right : Lean.Expr
  extended : ∀ expression : BooleanLocal, operation.booleanExpr left right ≠ expression.expr
  deriving Repr

namespace BooleanJoined

def expr (value : BooleanJoined) : Lean.Expr := value.operation.booleanExpr value.left value.right

theorem children_size (value : BooleanJoined) :
    sizeOf value.left < sizeOf value.expr ∧ sizeOf value.right < sizeOf value.expr := by
  rcases value with ⟨operation, left, right, extended⟩
  cases operation <;> simp [expr, Junction.booleanExpr] <;> omega

end BooleanJoined
end LeanExe.Source.Scalar
