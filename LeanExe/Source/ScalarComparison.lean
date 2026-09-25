import LeanExe.Source.ScalarDo

namespace LeanExe.Source.Scalar

/-- Canonical Lean comparison forms, with their native UInt64 meanings. -/
inductive Comparison where
  | eq | ne | lt | le | gt | ge | beq | bne
  | negate (comparison : Comparison)
  deriving DecidableEq, Repr

namespace Comparison

def denote : Comparison → UInt64 → UInt64 → Bool
  | .eq => fun x y => decide (x = y)
  | .ne => fun x y => decide (x ≠ y)
  | .lt => fun x y => decide (x < y)
  | .le => fun x y => decide (x ≤ y)
  | .gt => fun x y => decide (x > y)
  | .ge => fun x y => decide (x ≥ y)
  | .beq => fun x y => x == y
  | .bne => fun x y => x != y
  | .negate op => fun x y => !(denote op x y)

def boolExpr (op : Comparison) (a b : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const (if op = .bne then ``_root_.bne else ``BEq.beq) [.zero])
    (.const ``UInt64 []))
    (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``UInt64 []))
      (.const ``instDecidableEqUInt64 []))) a) b

def condition : Comparison → Lean.Expr → Lean.Expr → Lean.Expr
  | .eq, a, b => .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``UInt64 [])) a) b
  | .ne, a, b => .app (.app (.app (.const ``Ne [.succ .zero]) (.const ``UInt64 [])) a) b
  | .lt, a, b => .app (.app (.app (.app (.const ``LT.lt [.zero]) (.const ``UInt64 []))
      (.const ``instLTUInt64 [])) a) b
  | .le, a, b => .app (.app (.app (.app (.const ``LE.le [.zero]) (.const ``UInt64 []))
      (.const ``instLEUInt64 [])) a) b
  | .gt, a, b => .app (.app (.app (.app (.const ``GT.gt [.zero]) (.const ``UInt64 []))
      (.const ``instLTUInt64 [])) a) b
  | .ge, a, b => .app (.app (.app (.app (.const ``GE.ge [.zero]) (.const ``UInt64 []))
      (.const ``instLEUInt64 [])) a) b
  | .beq, a, b => .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
      (boolExpr .beq a b)) (.const ``Bool.true [])
  | .bne, a, b => .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
      (boolExpr .bne a b)) (.const ``Bool.true [])
  | .negate op, a, b => .app (.const ``Not []) (condition op a b)

def evidence : Comparison → Lean.Expr → Lean.Expr → Lean.Expr
  | .eq, a, b => .app (.app (.const ``instDecidableEqUInt64 []) a) b
  | .ne, a, b => .app (.app (.const ``instDecidableNot []) (condition .eq a b))
      (.app (.app (.const ``instDecidableEqUInt64 []) a) b)
  | .lt, a, b => .app (.app (.const ``UInt64.decLt []) a) b
  | .le, a, b => .app (.app (.const ``UInt64.decLe []) a) b
  | .gt, a, b => .app (.app (.const ``UInt64.decLt []) b) a
  | .ge, a, b => .app (.app (.const ``UInt64.decLe []) b) a
  | .beq, a, b => .app (.app (.const ``instDecidableEqBool []) (boolExpr .beq a b))
      (.const ``Bool.true [])
  | .bne, a, b => .app (.app (.const ``instDecidableEqBool []) (boolExpr .bne a b))
      (.const ``Bool.true [])
  | .negate op, a, b => .app (.app (.const ``instDecidableNot []) (op.condition a b))
      (evidence op a b)

theorem operands_size (op : Comparison) (a b : Lean.Expr) :
    sizeOf a < sizeOf (op.condition a b) ∧ sizeOf b < sizeOf (op.condition a b) := by
  induction op <;> simp_all [condition, boolExpr] <;> omega

/-- Exact ordinary `if` syntax over a supported comparison. Its decision
procedure is part of the grammar, including the compared operands. -/
def branch (op : Comparison) (a b onTrue onFalse : Lean.Expr)
    (type : ResultType := .word) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type.expr)
    (op.condition a b)) (op.evidence a b)) onTrue) onFalse

end Comparison
end LeanExe.Source.Scalar
