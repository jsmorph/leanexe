import LeanExe.Source.ScalarGuard
import LeanExe.Source.ScalarGuardDecision

namespace LeanExe.Source.Scalar

/-- Additional checked guard forms share the proved guard lowering. -/
inductive CompoundGuard where
  | reannotated (guard : ReannotatedGuard)
  | literal (value : GuardLiteral)
  | proposition (junction : Junction) (left right : Guard) (negations : Nat := 0)
  | boolean (junction : Junction) (left right : BooleanGuard) (negations : Nat := 0) (propNegations : Nat := 0)
  | savedLeft (junction : Junction) (left : SavedBooleanGuard) (right : Guard) (negations : Nat := 0)
  | savedRight (junction : Junction) (left : Guard) (right : SavedBooleanGuard) (negations : Nat := 0)
  | savedBoth (junction : Junction) (left right : SavedBooleanGuard) (negations : Nat := 0)
  | letGuard (binding : GuardLet) (body : Guard) (negations : Nat := 0)
  | letSaved (binding : GuardLet) (body : SavedBooleanGuard) (negations : Nat := 0)
  | localNegation (value : SavedBooleanGuard) (negations : Nat := 0)
  deriving Repr

namespace CompoundGuard

def tree : CompoundGuard → Guard
  | .reannotated guard => guard.tree
  | .literal value => .literal value
  | .proposition op a b n => .junction n op a b
  | .boolean op a b n m => .boolean m n op a b
  | .savedLeft op a b n => .savedLeft n op a b
  | .savedRight op a b n => .savedRight n op a b
  | .savedBoth op a b n => .savedBoth n op a b
  | .letGuard binding body n => .letGuard n binding body
  | .letSaved binding body n => .letSaved n binding body
  | .localNegation value n => .localNegation n value

abbrev operands (guard : CompoundGuard) : List Lean.Expr := guard.tree.operands
abbrev denote (guard : CompoundGuard) (native : Lean.Expr → UInt64) : Bool := guard.tree.denote native

abbrev condition (guard : CompoundGuard) : Lean.Expr := guard.tree.condition
def evidence : CompoundGuard → Lean.Expr
  | .reannotated guard => guard.evidence
  | guard => guard.tree.evidence

theorem operands_size (guard : CompoundGuard) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf guard.condition + guardOperandOverhead :=
  guard.tree.operands_size member

def branch (guard : CompoundGuard) (type onTrue onFalse : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type)
    guard.condition) guard.evidence) onTrue) onFalse

end CompoundGuard
end LeanExe.Source.Scalar
