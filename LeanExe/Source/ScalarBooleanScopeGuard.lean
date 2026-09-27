import LeanExe.Source.ScalarBooleanLocal

namespace LeanExe.Source.Scalar

/-- A Boolean condition whose expression needs the general scalar conversion. -/
structure BooleanScopeGuard where
  value : SavedBooleanGuard
  extended : ∀ expression : BooleanLocal, value.expr ≠ expression.expr
  deriving Repr

namespace BooleanScopeGuard
abbrev condition (guard : BooleanScopeGuard) := guard.value.condition
abbrev evidence (guard : BooleanScopeGuard) := guard.value.evidence
abbrev operand (guard : BooleanScopeGuard) := guard.value.operand

def branch (guard : BooleanScopeGuard) (type yes no : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type) guard.condition) guard.evidence) yes) no

def dependentBranch (guard : BooleanScopeGuard) (type : Lean.Expr)
    (trueName falseName : Lean.Name) (trueInfo falseInfo : Lean.BinderInfo) (yes no : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) type) guard.condition) guard.evidence)
    (.lam trueName guard.condition yes trueInfo)) (.lam falseName (.app (.const ``Not []) guard.condition) no falseInfo)

theorem operand_size (guard : BooleanScopeGuard) : sizeOf guard.operand < sizeOf guard.condition :=
  guard.value.operand_size

end BooleanScopeGuard
end LeanExe.Source.Scalar
