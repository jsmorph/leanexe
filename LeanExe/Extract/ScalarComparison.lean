import LeanExe.Source.ScalarComparison
import LeanExe.Source.ExprEquality
import LeanExe.IR.ScalarSemantics

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (Comparison)

/-- Recognize only the canonical comparison heads and standard UInt64 instances. -/
def comparisonOperands? : Lean.Expr → Option (Comparison × Lean.Expr × Lean.Expr)
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``UInt64 [])) a) b => some (.eq, a, b)
  | .app (.app (.app (.app (.const ``LT.lt [.zero]) (.const ``UInt64 []))
      (.const ``instLTUInt64 [])) a) b => some (.lt, a, b)
  | .app (.app (.app (.app (.const ``LE.le [.zero]) (.const ``UInt64 []))
      (.const ``instLEUInt64 [])) a) b => some (.le, a, b)
  | .app (.app (.app (.app (.const ``GT.gt [.zero]) (.const ``UInt64 []))
      (.const ``instLTUInt64 [])) a) b => some (.gt, a, b)
  | .app (.app (.app (.app (.const ``GE.ge [.zero]) (.const ``UInt64 []))
      (.const ``instLEUInt64 [])) a) b => some (.ge, a, b)
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
      (.app (.app (.app (.app (.const ``BEq.beq [.zero]) (.const ``UInt64 []))
        (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``UInt64 []))
          (.const ``instDecidableEqUInt64 []))) a) b)) (.const ``Bool.true []) => some (.beq, a, b)
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
      (.app (.app (.app (.app (.const ``_root_.bne [.zero]) (.const ``UInt64 []))
        (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``UInt64 []))
          (.const ``instDecidableEqUInt64 []))) a) b)) (.const ``Bool.true []) => some (.bne, a, b)
  | _ => none

@[simp] theorem comparisonOperands_condition (op : Comparison) (a b : Lean.Expr) :
    comparisonOperands? (op.condition a b) = some (op, a, b) := by
  cases op <;> rfl

theorem comparisonOperands_sound {condition a b : Lean.Expr} {op : Comparison}
    (h : comparisonOperands? condition = some (op, a, b)) : condition = op.condition a b := by
  unfold comparisonOperands? at h
  split at h <;> cases h <;> rfl

/-- Check the whole explicit decision procedure, including its operand expressions. -/
def comparison? (condition evidence : Lean.Expr) : Option (Comparison × Lean.Expr × Lean.Expr) := do
  let (op, a, b) ← comparisonOperands? condition
  if LeanExe.Source.ExprEquality.same evidence (op.evidence a b) then some (op, a, b) else none

@[simp] theorem comparison_accepts (op : Comparison) (a b : Lean.Expr) :
    comparison? (op.condition a b) (op.evidence a b) = some (op, a, b) := by
  simp [comparison?]

theorem comparison_sound {condition evidence a b : Lean.Expr} {op : Comparison}
    (h : comparison? condition evidence = some (op, a, b)) :
    condition = op.condition a b ∧ evidence = op.evidence a b := by
  simp only [comparison?, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨operation, left, right⟩, operands, matched⟩ := h
  split at matched
  · rename_i same
    cases matched
    exact ⟨comparisonOperands_sound operands, LeanExe.Source.ExprEquality.same_eq_true.mp same⟩
  · contradiction

theorem comparison_size {condition evidence a b : Lean.Expr} {op : Comparison}
    (h : comparison? condition evidence = some (op, a, b)) :
    sizeOf a < sizeOf condition ∧ sizeOf b < sizeOf condition := by
  rw [(comparison_sound h).1]
  exact op.operands_size a b

def lowerComparison : Comparison → LeanExe.IR.Expr → LeanExe.IR.Expr → LeanExe.IR.Cond
  | .eq, a, b => .eqU64 a b
  | .lt, a, b => .ltU64 a b
  | .le, a, b => .leU64 a b
  | .gt, a, b => .not (.leU64 a b)
  | .ge, a, b => .not (.ltU64 a b)
  | .beq, a, b => .eqU64 a b
  | .bne, a, b => .not (.eqU64 a b)

theorem lowerComparison_correct (op : Comparison)
    {a b : LeanExe.IR.Expr} {s s₁ s₂ : LeanExe.IR.ScalarStore} {x y : UInt64}
    (left : a.ScalarEval s x s₁) (right : b.ScalarEval s₁ y s₂) :
    (lowerComparison op a b).ScalarEval s (op.denote x y) s₂ := by
  cases op with
  | eq | beq => exact .eq left right
  | lt => exact .lt left right
  | le => exact .le left right
  | bne => exact .not (.eq left right)
  | gt => simpa [Comparison.denote, lowerComparison, ← decide_not] using LeanExe.IR.Cond.ScalarEval.not (.le left right)
  | ge => simpa [Comparison.denote, lowerComparison, ← decide_not] using LeanExe.IR.Cond.ScalarEval.not (.lt left right)

end LeanExe.Extract.Core
