import LeanExe.Source.ScalarBooleanComparison

namespace LeanExe.Source.Scalar

/-- Canonical Lean comparison forms, with their native UInt64 meanings. -/
inductive Comparison where
  | eq (type : ResultType := .word)
  | ne (type : ResultType := .word)
  | lt (type : ResultType := .word)
  | le (type : ResultType := .word)
  | gt (type : ResultType := .word)
  | ge (type : ResultType := .word)
  | beq | bne
  | negate (comparison : Comparison)
  | boolNot (comparison : BooleanComparison)
  deriving DecidableEq, Repr

namespace Comparison

def denote : Comparison → UInt64 → UInt64 → Bool
  | .eq _ => fun x y => decide (x = y)
  | .ne _ => fun x y => decide (x ≠ y)
  | .lt _ => fun x y => decide (x < y)
  | .le _ => fun x y => decide (x ≤ y)
  | .gt _ => fun x y => decide (x > y)
  | .ge _ => fun x y => decide (x ≥ y)
  | .beq => fun x y => x == y
  | .bne => fun x y => x != y
  | .negate op => fun x y => !(denote op x y)
  | .boolNot op => fun x y => !(op.denote x y)

def boolExpr (op : Comparison) (a b : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const (if op = .bne then ``_root_.bne else ``BEq.beq) [.zero])
    (.const ``UInt64 []))
    (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``UInt64 []))
      (.const ``instDecidableEqUInt64 []))) a) b

def condition : Comparison → Lean.Expr → Lean.Expr → Lean.Expr
  | .eq type, a, b => .app (.app (.app (.const ``Eq [.succ .zero]) type.expr) a) b
  | .ne type, a, b => .app (.app (.app (.const ``Ne [.succ .zero]) type.expr) a) b
  | .lt type, a, b => .app (.app (.app (.app (.const ``LT.lt [.zero]) type.expr)
      (.const ``instLTUInt64 [])) a) b
  | .le type, a, b => .app (.app (.app (.app (.const ``LE.le [.zero]) type.expr)
      (.const ``instLEUInt64 [])) a) b
  | .gt type, a, b => .app (.app (.app (.app (.const ``GT.gt [.zero]) type.expr)
      (.const ``instLTUInt64 [])) a) b
  | .ge type, a, b => .app (.app (.app (.app (.const ``GE.ge [.zero]) type.expr)
      (.const ``instLEUInt64 [])) a) b
  | .beq, a, b => .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
      (boolExpr .beq a b)) (.const ``Bool.true [])
  | .bne, a, b => .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
      (boolExpr .bne a b)) (.const ``Bool.true [])
  | .negate op, a, b => .app (.const ``Not []) (condition op a b)
  | .boolNot op, a, b => .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
      (.app (.const ``Bool.not []) (op.expr a b))) (.const ``Bool.true [])

def evidence : Comparison → Lean.Expr → Lean.Expr → Lean.Expr
  | .eq _, a, b => .app (.app (.const ``instDecidableEqUInt64 []) a) b
  | .ne type, a, b => .app (.app (.const ``instDecidableNot []) (condition (.eq type) a b))
      (.app (.app (.const ``instDecidableEqUInt64 []) a) b)
  | .lt _, a, b => .app (.app (.const ``UInt64.decLt []) a) b
  | .le _, a, b => .app (.app (.const ``UInt64.decLe []) a) b
  | .gt _, a, b => .app (.app (.const ``UInt64.decLt []) b) a
  | .ge _, a, b => .app (.app (.const ``UInt64.decLe []) b) a
  | .beq, a, b => .app (.app (.const ``instDecidableEqBool []) (boolExpr .beq a b))
      (.const ``Bool.true [])
  | .bne, a, b => .app (.app (.const ``instDecidableEqBool []) (boolExpr .bne a b))
      (.const ``Bool.true [])
  | .negate op, a, b => .app (.app (.const ``instDecidableNot []) (op.condition a b))
      (evidence op a b)
  | .boolNot op, a, b => .app (.app (.const ``instDecidableEqBool [])
      (.app (.const ``Bool.not []) (op.expr a b))) (.const ``Bool.true [])

theorem operands_size (op : Comparison) (a b : Lean.Expr) :
    sizeOf a < sizeOf (op.condition a b) ∧ sizeOf b < sizeOf (op.condition a b) := by
  induction op with
  | boolNot op =>
    have size := op.operands_size a b
    simp [condition] <;> omega
  | _ => simp_all [condition, boolExpr] <;> omega

/-- Exact ordinary `if` syntax over a supported comparison. Its decision
procedure is part of the grammar, including the compared operands. -/
def branch (op : Comparison) (a b onTrue onFalse : Lean.Expr)
    (type : ResultType := .word) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type.expr)
    (op.condition a b)) (op.evidence a b)) onTrue) onFalse

end Comparison
end LeanExe.Source.Scalar
