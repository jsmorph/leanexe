import LeanExe.Source.ScalarGuard

namespace LeanExe.Source.Scalar

/-- Both compound source forms share scalar operands and proved guard lowering. -/
inductive CompoundGuard where
  | proposition (junction : Junction) (left right : Guard) (negations : Nat := 0)
  | boolean (junction : Junction) (left right : BooleanGuard) (negations : Nat := 0)
  deriving Repr

namespace CompoundGuard

def tree : CompoundGuard → Guard
  | .proposition op a b n => .junction n op a b
  | .boolean op a b n => (BooleanGuard.junction n op a b).asGuard

abbrev operands (guard : CompoundGuard) : List Lean.Expr := guard.tree.operands
abbrev denote (guard : CompoundGuard) (native : Lean.Expr → UInt64) : Bool := guard.tree.denote native

def condition : CompoundGuard → Lean.Expr
  | .proposition op a b n => (Guard.junction n op a b).condition
  | .boolean op a b n => (BooleanGuard.junction n op a b).condition

def evidence : CompoundGuard → Lean.Expr
  | .proposition op a b n => (Guard.junction n op a b).evidence
  | .boolean op a b n => (BooleanGuard.junction n op a b).evidence

theorem operands_size (guard : CompoundGuard) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf guard.condition := by
  cases guard with
  | proposition op a b n => exact (Guard.junction n op a b).operands_size member
  | boolean op a b n =>
    have bound := (BooleanGuard.junction n op a b).operands_size (operand := operand)
      (by simpa [operands, tree] using member)
    simp only [condition, BooleanGuard.condition]
    simp_all; omega

def branch (guard : CompoundGuard) (type onTrue onFalse : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type)
    guard.condition) guard.evidence) onTrue) onFalse

end CompoundGuard
end LeanExe.Source.Scalar
