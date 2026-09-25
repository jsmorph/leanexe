import LeanExe.Extract.ScalarRangeInterval
import LeanExe.Source.ScalarRangeStride

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar.Range.Exit

/-- Ceiling division without adding the stride to a possibly maximal word. -/
def scalarRangeTrips (stride : Nat) (distance : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  if stride = 1 then distance else
    .ite (.eqU64 distance (.u64 0)) (.u64 0)
      (.u64Bin .add (.u64Bin .divU (.u64Bin .sub distance (.u64 1)) (.u64 stride)) (.u64 1))

/-- Unit steps retain the previous counter expression verbatim. -/
def scalarRangeScale (stride : Nat) (index : LeanExe.IR.Expr) : LeanExe.IR.Expr :=
  if stride = 1 then index else .u64Bin .mul (.u64 stride) index

theorem scalarRangeTrips_correct {stride : Nat} (positive : 0 < stride) (fits : stride < UInt64.size)
    {expression : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore} {distance : UInt64}
    (evaluated : expression.ScalarEval store distance store) :
    (scalarRangeTrips stride expression).ScalarEval store (UInt64.ofNat (trips distance.toNat stride)) store := by
  by_cases unit : stride = 1
  · simpa [scalarRangeTrips, unit, trips_one] using evaluated
  rw [scalarRangeTrips, ite_eq_right unit]
  by_cases zero : distance = 0
  · subst distance
    apply LeanExe.IR.Expr.ScalarEval.iteTrue
    · simpa using (LeanExe.IR.Cond.ScalarEval.eq evaluated (LeanExe.IR.Expr.ScalarEval.const (n := 0)))
    · simpa [trips_zero positive] using (LeanExe.IR.Expr.ScalarEval.const (s := store) (n := 0))
  · have distancePositive : 0 < distance.toNat := by
      have nonzero : distance.toNat ≠ 0 := by
        intro same
        apply zero
        apply UInt64.toNat_inj.mp
        simpa using same
      omega
    have predecessorSmall : distance.toNat - 1 < UInt64.size :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) distance.toNat_lt_size
    have predecessor : distance - UInt64.ofNat 1 = UInt64.ofNat (distance.toNat - 1) := by
      simpa only [UInt64.ofNat_toNat] using (UInt64.ofNat_sub (show 1 ≤ distance.toNat by omega)).symm
    have quotientSmall : (distance.toNat - 1) / stride < UInt64.size :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) predecessorSmall
    have quotient : UInt64.ofNat (distance.toNat - 1) / UInt64.ofNat stride =
        UInt64.ofNat ((distance.toNat - 1) / stride) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' predecessorSmall,
        UInt64.toNat_ofNat_of_lt' fits, UInt64.toNat_ofNat_of_lt' quotientSmall]
    apply LeanExe.IR.Expr.ScalarEval.iteFalse
    · simpa [Bool.beq_eq_decide_eq, zero] using (LeanExe.IR.Cond.ScalarEval.eq evaluated (LeanExe.IR.Expr.ScalarEval.const (n := 0)))
    · have subtract : (LeanExe.IR.Expr.u64Bin .sub expression (.u64 1)).ScalarEval store
          (UInt64.ofNat (distance.toNat - 1)) store := by
        simpa only [predecessor] using
          (LeanExe.IR.Expr.ScalarEval.bin (operation := .sub) evaluated (.const (n := 1)) rfl)
      have divide : (LeanExe.IR.Expr.u64Bin .divU (.u64Bin .sub expression (.u64 1)) (.u64 stride)).ScalarEval store
          (UInt64.ofNat ((distance.toNat - 1) / stride)) store := by
        simpa only [quotient] using
          (LeanExe.IR.Expr.ScalarEval.bin (operation := .divU) subtract (.const (n := stride)) rfl)
      simpa only [trips_nonzero distancePositive positive, UInt64.ofNat_add] using
        (LeanExe.IR.Expr.ScalarEval.bin (operation := .add) divide (.const (n := 1)) rfl)

theorem scalarRangeScale_correct (stride index : Nat)
    {expression : LeanExe.IR.Expr} {store : LeanExe.IR.ScalarStore}
    (evaluated : expression.ScalarEval store (UInt64.ofNat index) store) :
    (scalarRangeScale stride expression).ScalarEval store (UInt64.ofNat (stride * index)) store := by
  by_cases unit : stride = 1
  · simpa [scalarRangeScale, unit] using evaluated
  rw [scalarRangeScale, ite_eq_right unit]
  simpa only [UInt64.ofNat_mul] using
    (LeanExe.IR.Expr.ScalarEval.bin (operation := .mul) (.const (n := stride)) evaluated rfl)

theorem scalarRangeTrips_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (stride : Nat) {distance : LeanExe.IR.Expr} (holds : P distance) : P (scalarRangeTrips stride distance) := by
  unfold scalarRangeTrips
  split
  · exact holds
  · exact choice .eq distance (.u64 0) _ _ holds (literal 0) (literal 0)
      (binary .add _ (.u64 1)
        (binary .div _ (.u64 stride) (binary .sub distance (.u64 1) holds (literal 1)) (literal stride))
        (literal 1))

theorem scalarRangeScale_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (stride : Nat) {index : LeanExe.IR.Expr} (holds : P index) : P (scalarRangeScale stride index) := by
  unfold scalarRangeScale
  split
  · exact holds
  · exact binary .mul (.u64 stride) index (literal stride) holds

end LeanExe.Extract.Core
