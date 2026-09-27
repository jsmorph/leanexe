import LeanExe.Source.ScalarBooleanLocal

namespace LeanExe.Source.Scalar

/-- Exact local predicate declaration before its Boolean continuation. -/
def booleanHelperExpr (booleanInput : Bool) (shape : BooleanFunctionBinding)
    (parameterName : Lean.Name) (body continuation : Lean.Expr) : Lean.Expr :=
  let input := Lean.Expr.const (if booleanInput then ``Bool else ``UInt64) []
  .letE shape.functionName (.forallE shape.typeName input shape.result.expr shape.typeInfo)
    (.lam parameterName input body shape.valueInfo) continuation shape.nondep

/-- Helper scopes outside the existing direct-call Boolean expression grammar. -/
structure BooleanHelper (booleanInput : Bool) where
  shape : BooleanFunctionBinding
  parameterName : Lean.Name
  body : BooleanLocal
  continuation : Lean.Expr
  extended : ∀ expression : BooleanLocal,
    booleanHelperExpr booleanInput shape parameterName body.expr continuation ≠ expression.expr
  deriving Repr

namespace BooleanHelper

def expr (value : BooleanHelper booleanInput) : Lean.Expr :=
  booleanHelperExpr booleanInput value.shape value.parameterName value.body.expr value.continuation

theorem body_size (value : BooleanHelper booleanInput) : sizeOf value.body.expr < sizeOf value.expr := by
  simp [expr, booleanHelperExpr]; omega

theorem continuation_size (value : BooleanHelper booleanInput) : sizeOf value.continuation < sizeOf value.expr := by
  simp [expr, booleanHelperExpr]; omega

end BooleanHelper
end LeanExe.Source.Scalar
