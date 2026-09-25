import LeanExe.Extract.ScalarComparison
import LeanExe.Extract.ScalarPrimitive

namespace LeanExe.Extract.Core

/-- Natural interval length. Keep the established zero-start output unchanged. -/
def scalarRangeDistance (first : Nat) (stop : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  if first = 0 then stop else
    .ite (.ltU64 (.u64 first) stop) (.u64Bin .sub stop (.u64 first)) (.u64 0)

/-- The native range index is the first index plus the internal loop counter. -/
def scalarRangeOffset (first : Nat) (index : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  if first = 0 then index else .u64Bin .add (.u64 first) index

theorem scalarRangeDistance_correct {first : Nat} (fits : first < UInt64.size)
    {stop : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore} {bound : UInt64}
    (evaluated : stop.ScalarEval store bound store) :
    (scalarRangeDistance first stop).ScalarEval store (UInt64.ofNat (bound.toNat - first)) store := by
  by_cases zero : first = 0
  · simpa [scalarRangeDistance, zero] using evaluated
  rw [scalarRangeDistance, ite_eq_right zero]
  have represented := UInt64.toNat_ofNat_of_lt' fits
  by_cases below : first < bound.toNat
  · have ordered : UInt64.ofNat first ≤ bound := by
      simpa [UInt64.le_iff_toNat_le, represented] using Nat.le_of_lt below
    have small : bound.toNat - first < UInt64.size :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) bound.toNat_lt_size
    have difference : bound - UInt64.ofNat first = UInt64.ofNat (bound.toNat - first) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ ordered, represented, UInt64.toNat_ofNat_of_lt' small]
    apply LeanExe.IR.Expr.ScalarEval.iteTrue
    · simpa [UInt64.lt_iff_toNat_lt, represented, below] using
        (LeanExe.IR.Cond.ScalarEval.lt (a := .u64 first) .const evaluated)
    · simpa only [difference] using
        (LeanExe.IR.Expr.ScalarEval.bin (operation := .sub) evaluated
          (LeanExe.IR.Expr.ScalarEval.const (n := first)) rfl)
  · have empty : bound.toNat - first = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt below)
    apply LeanExe.IR.Expr.ScalarEval.iteFalse
    · simpa [UInt64.lt_iff_toNat_lt, represented, below] using
        (LeanExe.IR.Cond.ScalarEval.lt (a := .u64 first) .const evaluated)
    · simpa [empty] using (LeanExe.IR.Expr.ScalarEval.const (s := store) (n := 0))

theorem scalarRangeOffset_correct (first index : Nat)
    {expression : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore}
    (evaluated : expression.ScalarEval store (UInt64.ofNat index) store) :
    (scalarRangeOffset first expression).ScalarEval store (UInt64.ofNat (first + index)) store := by
  by_cases zero : first = 0
  · simpa [scalarRangeOffset, zero] using evaluated
  rw [scalarRangeOffset, ite_eq_right zero]
  have addition : UInt64.ofNat first + UInt64.ofNat index = UInt64.ofNat (first + index) := by
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.add_mod]
  simpa only [addition] using (LeanExe.IR.Expr.ScalarEval.bin (operation := .add)
    (LeanExe.IR.Expr.ScalarEval.const (n := first)) evaluated rfl)

theorem scalarRangeDistance_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (first : Nat) {stop : LeanExe.IR.Expr} (holds : P stop) : P (scalarRangeDistance first stop) := by
  unfold scalarRangeDistance
  split
  · exact holds
  · exact choice .lt (.u64 first) stop _ _ (literal first) holds
      (binary .sub stop (.u64 first) holds (literal first)) (literal 0)

theorem scalarRangeOffset_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (first : Nat) {index : LeanExe.IR.Expr} (holds : P index) : P (scalarRangeOffset first index) := by
  unfold scalarRangeOffset
  split
  · exact holds
  · exact binary .add (.u64 first) index (literal first) holds

end LeanExe.Extract.Core
