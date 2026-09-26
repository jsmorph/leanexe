import LeanExe.Source.ScalarDo

namespace LeanExe.Source.Scalar

/-- Boolean comparisons retain their actual Bool syntax, including repeated `!`. -/
inductive BooleanComparison where
  | eq | ne
  | negate (comparison : BooleanComparison)
  deriving DecidableEq, Repr

namespace BooleanComparison

def denote : BooleanComparison → UInt64 → UInt64 → Bool
  | .eq => fun x y => x == y
  | .ne => fun x y => x != y
  | .negate op => fun x y => !(op.denote x y)

def positive : BooleanComparison → Bool
  | .eq => true
  | .ne => false
  | .negate op => !op.positive

def atom (unequal : Bool) (a b : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const (if unequal then ``_root_.bne else ``BEq.beq) [.zero])
    (.const ``UInt64 []))
    (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``UInt64 []))
      (.const ``instDecidableEqUInt64 []))) a) b

def expr : BooleanComparison → Lean.Expr → Lean.Expr → Lean.Expr
  | .eq, a, b => atom false a b
  | .ne, a, b => atom true a b
  | .negate op, a, b => .app (.const ``Bool.not []) (op.expr a b)

theorem denote_polarity (op : BooleanComparison) (x y : UInt64) :
    op.denote x y = if op.positive then x == y else !(x == y) := by
  induction op with
  | eq | ne => rfl
  | negate op ih =>
    cases h : op.positive <;> simp [denote, positive, ih, h]

theorem operands_size (op : BooleanComparison) (a b : Lean.Expr) :
    sizeOf a < sizeOf (op.expr a b) ∧ sizeOf b < sizeOf (op.expr a b) := by
  induction op <;> simp_all [expr, atom] <;> omega

end BooleanComparison
end LeanExe.Source.Scalar
