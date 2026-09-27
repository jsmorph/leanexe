import LeanExe.Source.ScalarBooleanLocal
import LeanExe.Source.ScalarPublicArgument

namespace LeanExe.Source.Scalar

/-- Exact scalar let syntax around an independently checked Boolean continuation. -/
structure BooleanScopeBinding (booleanInput : Bool) where
  name : Lean.Name
  domain : Lean.Expr
  input : PublicArgument.Domain (if booleanInput then .boolean else .word) domain
  value : Lean.Expr
  body : Lean.Expr
  nondep : Bool
  extended : ∀ expression : BooleanLocal,
    Lean.Expr.letE name domain value body nondep ≠ expression.expr
  deriving Repr

namespace BooleanScopeBinding

def expr (binding : BooleanScopeBinding booleanInput) : Lean.Expr :=
  .letE binding.name binding.domain binding.value binding.body binding.nondep

theorem value_size (binding : BooleanScopeBinding booleanInput) : sizeOf binding.value < sizeOf binding.expr := by
  simp [expr]; omega

theorem body_size (binding : BooleanScopeBinding booleanInput) : sizeOf binding.body < sizeOf binding.expr := by
  simp [expr]; omega

end BooleanScopeBinding
end LeanExe.Source.Scalar
