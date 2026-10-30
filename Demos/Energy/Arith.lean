import Demos.Energy.Program
import Demos.Energy.Words

/-! The authorizer's word operations as natural-number operations.  Under the validity bounds no
sum, product, or difference that the authorizer computes leaves the range of `UInt64`, so each
operation equals the operation on the words' natural numbers.  The checks before the side tests
accept exactly the inputs of `InputValid`. -/

namespace Demos.Energy.Arith

open Words

theorem toNat_min (a b : UInt64) : (min a b).toNat = min a.toNat b.toNat := by
  show (if a ≤ b then a else b).toNat = _
  split <;> rename_i h <;> rw [UInt64.le_iff_toNat_le] at h <;> omega

theorem toNat_max (a b : UInt64) : (max a b).toNat = max a.toNat b.toNat := by
  show (if a ≤ b then b else a).toNat = _
  split <;> rename_i h <;> rw [UInt64.le_iff_toNat_le] at h <;> omega

theorem toNat_add {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem toNat_sub {a b : UInt64} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le a b (UInt64.le_iff_toNat_le.mpr h)

theorem toNat_mul {a b : UInt64} (h : a.toNat * b.toNat < 2 ^ 64) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul]
  exact Nat.mod_eq_of_lt h

@[simp] theorem word_eq (xs : Array UInt64) (i : UInt64) : word xs i = xs[i.toNat]! := rfl

theorem rangeOk_iff (xs : Array UInt64) : rangeOk xs = true ↔
    xs[1]!.toNat < 2 ^ 40 ∧ xs[2]!.toNat ≤ 2 ^ 42 ∧ xs[3]!.toNat ≤ 2 ^ 42 ∧
      xs[4]!.toNat ≤ 1 ∧ PowerWord xs[5]! ∧ xs[6]!.toNat ≤ 2 ^ 20 ∧ xs[7]!.toNat ≤ 2 ^ 20 ∧
      xs[8]!.toNat ≤ 2 ^ 20 ∧ xs[9]!.toNat ≤ 2 ^ 20 ∧ PowerWord xs[10]! := by
  simp only [rangeOk, powerOk, word_eq, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, PowerWord, timeBound, energyBound,
    powerBound, offset, UInt64.toNat_ofNat, UInt64.reduceSub, UInt64.reduceAdd]
  norm_num
  constructor <;> intro h <;> omega

theorem orderOk_iff (xs : Array UInt64) : orderOk xs = true ↔
    xs[2]!.toNat ≤ xs[3]!.toNat ∧ xs[6]!.toNat ≤ xs[7]!.toNat ∧ xs[8]!.toNat ≤ xs[9]!.toNat := by
  simp only [orderOk, word_eq, Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
    UInt64.toNat_ofNat]
  norm_num
  constructor <;> intro h <;> omega

theorem limitOk_iff {site : Array UInt64} (hs : ProfileValid site) (xs : Array UInt64) :
    limitOk site xs = true ↔
      2 ^ 32 - site[4]!.toNat ≤ xs[10]!.toNat ∧ xs[10]!.toNat ≤ 2 ^ 32 + site[3]!.toNat := by
  have h4 := hs.discharge
  have h3 := hs.charge
  have e1 : ((4294967296 : UInt64) - site[4]!).toNat = 4294967296 - site[4]!.toNat :=
    toNat_sub (by rw [show (4294967296 : UInt64).toNat = 4294967296 from rfl]; omega)
  have e2 : ((4294967296 : UInt64) + site[3]!).toNat = 4294967296 + site[3]!.toNat :=
    toNat_add (by rw [show (4294967296 : UInt64).toNat = 4294967296 from rfl]; omega)
  simp only [limitOk, word_eq, offset, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, show (3 : UInt64).toNat = 3 from rfl,
    show (4 : UInt64).toNat = 4 from rfl, show (10 : UInt64).toNat = 10 from rfl]
  rw [e1, e2]
  constructor <;> intro h <;> omega

end Demos.Energy.Arith
