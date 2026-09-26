import LeanExe.Source.ScalarGuardDecision

namespace LeanExe.Source.Scalar

/-- A guard with its independently checked standard decision expression. -/
structure DecidedGuard where
  tree : Guard
  evidence : Lean.Expr
  meaning : GuardDecision tree evidence
  deriving Repr

namespace DecidedGuard

def canonical (tree : Guard) : DecidedGuard := ⟨tree, tree.evidence, .canonical tree⟩

abbrev condition (guard : DecidedGuard) := guard.tree.condition
abbrev operands (guard : DecidedGuard) := guard.tree.operands
abbrev denote (guard : DecidedGuard) (native : Lean.Expr → UInt64) := guard.tree.denote native

theorem operands_size (guard : DecidedGuard) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf guard.condition :=
  guard.tree.operands_size member

end DecidedGuard

instance : Coe DecidedGuard Guard := ⟨DecidedGuard.tree⟩

end LeanExe.Source.Scalar
