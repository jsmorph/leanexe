import LeanExe.Source.ScalarComparison
import LeanExe.Extract.ScalarBooleanComparison
import LeanExe.Extract.ScalarDo
import LeanExe.Source.ExprEquality
import LeanExe.IR.ScalarSemantics

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (Comparison)

/-- Recognize only the canonical comparison heads and standard UInt64 instances. -/
def comparisonOperands? : Lean.Expr → Option (Comparison × Lean.Expr × Lean.Expr)
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
      (.app (.app (.app (.app (.const ``BEq.beq [.zero]) (.const ``UInt64 []))
        (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``UInt64 []))
          (.const ``instDecidableEqUInt64 []))) a) b)) (.const ``Bool.true []) => some (.beq, a, b)
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
      (.app (.app (.app (.app (.const ``_root_.bne [.zero]) (.const ``UInt64 []))
        (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``UInt64 []))
          (.const ``instDecidableEqUInt64 []))) a) b)) (.const ``Bool.true []) => some (.bne, a, b)
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
      (.app (.const ``Bool.not []) inner)) (.const ``Bool.true []) =>
      (booleanComparisonOperands? inner).map fun (op, a, b) => (.boolNot op, a, b)
  | .app (.app (.app (.const ``Eq [.succ .zero]) type) a) b =>
      (scalarResultType? type).map fun result => (.eq result, a, b)
  | .app (.app (.app (.const ``Ne [.succ .zero]) type) a) b =>
      (scalarResultType? type).map fun result => (.ne result, a, b)
  | .app (.app (.app (.app (.const ``LT.lt [.zero]) type)
      (.const ``instLTUInt64 [])) a) b =>
      (scalarResultType? type).map fun result => (.lt result, a, b)
  | .app (.app (.app (.app (.const ``LE.le [.zero]) type)
      (.const ``instLEUInt64 [])) a) b =>
      (scalarResultType? type).map fun result => (.le result, a, b)
  | .app (.app (.app (.app (.const ``GT.gt [.zero]) type)
      (.const ``instLTUInt64 [])) a) b =>
      (scalarResultType? type).map fun result => (.gt result, a, b)
  | .app (.app (.app (.app (.const ``GE.ge [.zero]) type)
      (.const ``instLEUInt64 [])) a) b =>
      (scalarResultType? type).map fun result => (.ge result, a, b)
  | .app (.const ``Not []) condition =>
      (comparisonOperands? condition).map fun (op, a, b) => (.negate op, a, b)
  | _ => none

@[simp] theorem comparisonOperands_condition (op : Comparison) (a b : Lean.Expr) :
    comparisonOperands? (op.condition a b) = some (op, a, b) := by
  induction op with
  | negate op ih => simp [Comparison.condition, comparisonOperands?, ih]
  | boolNot op => simp [Comparison.condition, comparisonOperands?]
  | eq type => cases type <;> simp [Comparison.condition, comparisonOperands?, LeanExe.Source.Scalar.ResultType.expr, scalarResultType?]
  | _ => simp [Comparison.condition, Comparison.boolExpr, comparisonOperands?]

theorem comparisonOperands_sound {condition a b : Lean.Expr} {op : Comparison}
    (h : comparisonOperands? condition = some (op, a, b)) : condition = op.condition a b := by
  induction condition using comparisonOperands?.induct generalizing op a b with
  | case1 | case2 => cases h; rfl
  | case3 inner =>
    rw [comparisonOperands?] at h
    obtain ⟨⟨innerOp, left, right⟩, found, same⟩ := Option.map_eq_some_iff.mp h
    cases same
    simp [Comparison.condition, booleanComparisonOperands_sound found]
  | case4 type left right excludedBeq excludedBne excludedNot =>
    rw [comparisonOperands?] at h
    · obtain ⟨result, found, same⟩ := Option.map_eq_some_iff.mp h
      cases same
      simp [Comparison.condition, scalarResultType_sound found]
    all_goals assumption
  | case5 type left right =>
    rw [comparisonOperands?] at h
    obtain ⟨result, found, same⟩ := Option.map_eq_some_iff.mp h
    cases same
    simp [Comparison.condition, scalarResultType_sound found]
  | case6 type left right =>
    rw [comparisonOperands?] at h
    obtain ⟨result, found, same⟩ := Option.map_eq_some_iff.mp h
    cases same
    simp [Comparison.condition, scalarResultType_sound found]
  | case7 type left right =>
    rw [comparisonOperands?] at h
    obtain ⟨result, found, same⟩ := Option.map_eq_some_iff.mp h
    cases same
    simp [Comparison.condition, scalarResultType_sound found]
  | case8 type left right =>
    rw [comparisonOperands?] at h
    obtain ⟨result, found, same⟩ := Option.map_eq_some_iff.mp h
    cases same
    simp [Comparison.condition, scalarResultType_sound found]
  | case9 type left right =>
    rw [comparisonOperands?] at h
    obtain ⟨result, found, same⟩ := Option.map_eq_some_iff.mp h
    cases same
    simp [Comparison.condition, scalarResultType_sound found]
  | case10 inner ih =>
    rw [comparisonOperands?] at h
    obtain ⟨⟨innerOp, left, right⟩, found, same⟩ := Option.map_eq_some_iff.mp h
    cases same
    simp [Comparison.condition, ih found]
  | case11 condition h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    rw [comparisonOperands?] at h <;> first | assumption | contradiction

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
  | .eq _, a, b => .eqU64 a b
  | .ne _, a, b => .not (.eqU64 a b)
  | .lt _, a, b => .ltU64 a b
  | .le _, a, b => .leU64 a b
  | .gt _, a, b => .not (.leU64 a b)
  | .ge _, a, b => .not (.ltU64 a b)
  | .beq, a, b => .eqU64 a b
  | .bne, a, b => .not (.eqU64 a b)
  | .negate op, a, b => .not (lowerComparison op a b)
  | .boolNot op, a, b => if op.positive then .not (.eqU64 a b) else .eqU64 a b

theorem lowerComparison_correct (op : Comparison)
    {a b : LeanExe.IR.Expr} {s s₁ s₂ : LeanExe.IR.ScalarStore} {x y : UInt64}
    (left : a.ScalarEval s x s₁) (right : b.ScalarEval s₁ y s₂) :
    (lowerComparison op a b).ScalarEval s (op.denote x y) s₂ := by
  induction op with
  | eq type => exact .eq left right
  | beq => exact .eq left right
  | lt type => exact .lt left right
  | le type => exact .le left right
  | bne => exact .not (.eq left right)
  | ne type => simpa only [Comparison.denote, lowerComparison, decide_not, Bool.beq_eq_decide_eq] using LeanExe.IR.Cond.ScalarEval.not (.eq left right)
  | negate op ih => exact .not ih
  | boolNot op =>
    cases h : op.positive
    · simpa [Comparison.denote, lowerComparison, op.denote_polarity, h,
        Bool.beq_eq_decide_eq] using LeanExe.IR.Cond.ScalarEval.eq left right
    · simpa [Comparison.denote, lowerComparison, op.denote_polarity, h,
        Bool.beq_eq_decide_eq] using LeanExe.IR.Cond.ScalarEval.not (.eq left right)
  | gt type => simpa [Comparison.denote, lowerComparison, ← decide_not] using LeanExe.IR.Cond.ScalarEval.not (.le left right)
  | ge type => simpa [Comparison.denote, lowerComparison, ← decide_not] using LeanExe.IR.Cond.ScalarEval.not (.lt left right)

end LeanExe.Extract.Core
