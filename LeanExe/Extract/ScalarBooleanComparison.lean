import LeanExe.Source.ScalarBooleanComparison

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (BooleanComparison)

/-- Only the standard UInt64 Boolean equality instances and Bool.not are admitted. -/
def booleanComparisonOperands? : Lean.Expr → Option (BooleanComparison × Lean.Expr × Lean.Expr)
  | .app (.app (.app (.app (.const ``BEq.beq [.zero]) (.const ``UInt64 []))
      (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``UInt64 []))
        (.const ``instDecidableEqUInt64 []))) a) b => some (.eq, a, b)
  | .app (.app (.app (.app (.const ``_root_.bne [.zero]) (.const ``UInt64 []))
      (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``UInt64 []))
        (.const ``instDecidableEqUInt64 []))) a) b => some (.ne, a, b)
  | .app (.const ``Bool.not []) inner =>
      (booleanComparisonOperands? inner).map fun (op, a, b) => (.negate op, a, b)
  | _ => none

@[simp] theorem booleanComparisonOperands_expr (op : BooleanComparison) (a b : Lean.Expr) :
    booleanComparisonOperands? (op.expr a b) = some (op, a, b) := by
  induction op with
  | negate op ih => simp [BooleanComparison.expr, booleanComparisonOperands?, ih]
  | _ => rfl

theorem booleanComparisonOperands_sound {expression a b : Lean.Expr} {op : BooleanComparison}
    (h : booleanComparisonOperands? expression = some (op, a, b)) : expression = op.expr a b := by
  induction expression using booleanComparisonOperands?.induct generalizing op a b with
  | case1 | case2 => cases h; rfl
  | case3 inner ih =>
    rw [booleanComparisonOperands?] at h
    obtain ⟨⟨innerOp, left, right⟩, found, same⟩ := Option.map_eq_some_iff.mp h
    cases same
    simp [BooleanComparison.expr, ih found]
  | case4 expression h1 h2 h3 =>
    rw [booleanComparisonOperands?] at h <;> first | assumption | contradiction

end LeanExe.Extract.Core
