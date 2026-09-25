import LeanExe.Source.ScalarGuard

namespace LeanExe.Source.Scalar

/-- Both compound source forms share scalar operands and proved guard lowering. -/
inductive CompoundGuard where
  | proposition (junction : Junction) (left right : Guard) (negations : Nat := 0)
  | boolean (junction : Junction) (left right : BooleanGuard) (negations : Nat := 0) (propNegations : Nat := 0)
  deriving Repr

namespace CompoundGuard

def tree : CompoundGuard → Guard
  | .proposition op a b n => .junction n op a b
  | .boolean op a b n m => .boolean m n op a b

abbrev operands (guard : CompoundGuard) : List Lean.Expr := guard.tree.operands
abbrev denote (guard : CompoundGuard) (native : Lean.Expr → UInt64) : Bool := guard.tree.denote native

abbrev condition (guard : CompoundGuard) : Lean.Expr := guard.tree.condition
abbrev evidence (guard : CompoundGuard) : Lean.Expr := guard.tree.evidence

theorem operands_size (guard : CompoundGuard) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf guard.condition :=
  guard.tree.operands_size member

def branch (guard : CompoundGuard) (type onTrue onFalse : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type)
    guard.condition) guard.evidence) onTrue) onFalse

end CompoundGuard
end LeanExe.Source.Scalar
