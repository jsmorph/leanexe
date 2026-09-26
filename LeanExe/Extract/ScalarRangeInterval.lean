import LeanExe.Extract.ScalarComparison
import LeanExe.Extract.ScalarPrimitive

namespace LeanExe.Extract.Core

/-- Natural interval length. Keep the established zero-start output unchanged. -/
def scalarRangeDistance (first stop : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  match first with
  | .u64 0 => stop
  | _ => .ite (.ltU64 first stop) (.u64Bin .sub stop first) (.u64 0)

/-- The native range index is the first index plus the internal loop counter. -/
def scalarRangeOffset (first index : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  match first with
  | .u64 0 => index
  | _ => .u64Bin .add first index

theorem scalarRangeDistance_correct {first stop : LeanExe.IR.Expr}
    {store : LeanExe.IR.ScalarStore} {begin bound : UInt64}
    (evaluatedFirst : first.ScalarEval store begin store)
    (evaluatedStop : stop.ScalarEval store bound store) :
    (scalarRangeDistance first stop).ScalarEval store
      (UInt64.ofNat (bound.toNat - begin.toNat)) store := by
  unfold scalarRangeDistance
  split
  · cases evaluatedFirst
    simpa using evaluatedStop
  · by_cases below : begin < bound
    · have ordered : begin ≤ bound := UInt64.le_of_lt below
      have small : bound.toNat - begin.toNat < UInt64.size :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) bound.toNat_lt_size
      have difference : bound - begin = UInt64.ofNat (bound.toNat - begin.toNat) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ ordered, UInt64.toNat_ofNat_of_lt' small]
      apply LeanExe.IR.Expr.ScalarEval.iteTrue
      · simpa [below] using (LeanExe.IR.Cond.ScalarEval.lt evaluatedFirst evaluatedStop)
      · simpa only [difference] using
          (LeanExe.IR.Expr.ScalarEval.bin (operation := .sub) evaluatedStop evaluatedFirst rfl)
    · have empty : bound.toNat - begin.toNat = 0 :=
        Nat.sub_eq_zero_of_le (Nat.le_of_not_gt (by simpa [UInt64.lt_iff_toNat_lt] using below))
      apply LeanExe.IR.Expr.ScalarEval.iteFalse
      · simpa [below] using (LeanExe.IR.Cond.ScalarEval.lt evaluatedFirst evaluatedStop)
      · simpa [empty] using (LeanExe.IR.Expr.ScalarEval.const (s := store) (n := 0))

theorem scalarRangeOffset_correct {first expression : LeanExe.IR.Expr}
    (index : Nat) {store : LeanExe.IR.ScalarStore} {begin : UInt64}
    (evaluatedFirst : first.ScalarEval store begin store)
    (evaluatedIndex : expression.ScalarEval store (UInt64.ofNat index) store) :
    (scalarRangeOffset first expression).ScalarEval store
      (UInt64.ofNat (begin.toNat + index)) store := by
  unfold scalarRangeOffset
  split
  · cases evaluatedFirst
    simpa using evaluatedIndex
  · have addition : begin + UInt64.ofNat index = UInt64.ofNat (begin.toNat + index) := by
      apply UInt64.toNat_inj.mp
      simp [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.add_mod]
    simpa only [addition] using (LeanExe.IR.Expr.ScalarEval.bin (operation := .add)
      evaluatedFirst evaluatedIndex rfl)

theorem scalarRangeDistance_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    {first stop : LeanExe.IR.Expr} (firstHolds : P first) (stopHolds : P stop) :
    P (scalarRangeDistance first stop) := by
  unfold scalarRangeDistance
  split
  · exact stopHolds
  · exact choice .lt first stop _ _ firstHolds stopHolds
      (binary .sub stop first stopHolds firstHolds) (literal 0)

theorem scalarRangeOffset_holds (P : LeanExe.IR.Expr → Prop)
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    {first index : LeanExe.IR.Expr} (firstHolds : P first) (indexHolds : P index) :
    P (scalarRangeOffset first index) := by
  unfold scalarRangeOffset
  split
  · exact indexHolds
  · exact binary .add first index firstHolds indexHolds

end LeanExe.Extract.Core
