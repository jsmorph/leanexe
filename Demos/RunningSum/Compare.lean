import Demos.RunningSum.Magnitude

namespace Demos.RunningSum

open Magnitude

theorem magnitude_lt_pow (digits : Array UInt64) (valid : DecimalDigits digits) :
    magnitude digits < 10 ^ digits.size := by
  rw [← lowValue_size]
  exact lowValue_lt digits valid digits.size

theorem magnitude_ge_pow (digits : Array UInt64) (valid : NormalDigits digits) (nonempty : 0 < digits.size) :
    10 ^ (digits.size - 1) ≤ magnitude digits := by
  have leading : 1 ≤ digit digits (digits.size - 1) := by
    rcases valid.2 with zero | positive
    · omega
    · have byte := valid.1 0 nonempty
      simp only [digit, show digits.size - 1 < digits.size by omega, ite_true, digitValue]
      rw [show digits.size - 1 - (digits.size - 1) = 0 by omega]
      omega
  have size : digits.size = (digits.size - 1) + 1 := by omega
  rw [← lowValue_size, size, lowValue]
  simp only [Nat.add_sub_cancel]
  have hp : 0 < 10 ^ (digits.size - 1) := by positivity
  nlinarith

theorem magnitude_positive (digits : Array UInt64) (valid : NormalDigits digits)
    (nonempty : digits.size ≠ 0) : 0 < magnitude digits := by
  have lower := magnitude_ge_pow digits valid (by omega)
  have positive : 0 < 10 ^ (digits.size - 1) := by positivity
  omega

theorem magnitude_eq_zero_iff (digits : Array UInt64) (valid : NormalDigits digits) :
    magnitude digits = 0 ↔ digits.size = 0 := by
  constructor
  · intro zero
    by_contra nonempty
    have := magnitude_positive digits valid nonempty
    omega
  · intro zero
    rw [← lowValue_size, zero]
    rfl

theorem magnitude_lt_of_size (a b : Array UInt64) (ha : NormalDigits a) (hb : NormalDigits b)
    (size : a.size < b.size) : magnitude a < magnitude b := by
  have upper := magnitude_lt_pow a ha.1
  have lower := magnitude_ge_pow b hb (by omega)
  have powers : 10 ^ a.size ≤ 10 ^ (b.size - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem high_digits_equal (a b : Array UInt64) (n m : Nat) (bound : n ≤ m)
    (same : ∀ i, n ≤ i → i < m → digit a i = digit b i) :
    lowValue a m + lowValue b n = lowValue b m + lowValue a n := by
  induction m with
  | zero =>
      have zero : n = 0 := by omega
      simp [zero, lowValue]
  | succ m ih =>
      by_cases last : n = m + 1
      · subst n
        omega
      · have previous := ih (by omega) (fun i hi him => same i hi (by omega))
        have digitEq := same m (by omega) (by omega)
        simp only [lowValue, digitEq]
        omega

theorem magnitude_eq_of_digits (a b : Array UInt64) (size : a.size = b.size)
    (same : ∀ i, i < a.size → a[i]! = b[i]!) : magnitude a = magnitude b := by
  have equality := high_digits_equal a b 0 a.size (by omega) (by
    intro i _ hi
    simp only [digit, hi, ← size, ite_true]
    rw [same _ (by omega)])
  have bValue : lowValue b a.size = magnitude b := by rw [size, lowValue_size]
  rw [lowValue_size a, bValue, show lowValue a 0 = 0 from rfl,
    show lowValue b 0 = 0 from rfl] at equality
  omega

theorem magnitude_lt_of_first (a b : Array UInt64) (ha : DecimalDigits a) (hb : DecimalDigits b)
    (size : a.size = b.size) (k : Nat) (index : k < a.size)
    (same : ∀ i, i < k → a[i]! = b[i]!) (less : a[k]!.toNat < b[k]!.toNat) :
    magnitude a < magnitude b := by
  let n := a.size - 1 - k
  have hn : n < a.size := by dsimp [n]; omega
  have indexEq : a.size - 1 - n = k := by dsimp [n]; omega
  have da : digit a n = a[k]!.toNat - 48 := by simp [digit, hn, indexEq, digitValue]
  have db : digit b n = b[k]!.toNat - 48 := by simp [digit, ← size, hn, indexEq, digitValue]
  have byteA := ha k index
  have byteB := hb k (by omega)
  have gap : digit a n + 1 ≤ digit b n := by rw [da, db]; omega
  have lowA := lowValue_lt a ha n
  have lowB := lowValue_lt b hb n
  have hp : 0 < 10 ^ n := by positivity
  have lowLess : lowValue a (n + 1) < lowValue b (n + 1) := by
    simp only [lowValue]
    nlinarith
  have equality := high_digits_equal a b (n + 1) a.size (by omega) (by
    intro i hi him
    have earlier : a.size - 1 - i < k := by dsimp [n] at hi; omega
    simp only [digit, him, ← size, ite_true]
    rw [same _ earlier])
  have bValue : lowValue b a.size = magnitude b := by rw [size, lowValue_size]
  rw [lowValue_size a, bValue] at equality
  omega

namespace Magnitude

def ComparePrefix (a b : Array UInt64) (n : Nat) (order : UInt64) : Prop :=
  (order = 0 ∧ ∀ i, i < n → a[i]! = b[i]!) ∨
    (order = 1 ∧ magnitude a < magnitude b) ∨ (order = 2 ∧ magnitude b < magnitude a)

def compareStep (a b : Array UInt64) (i order : UInt64) : UInt64 :=
  if order != 0 then order
  else if a[i.toNat]! < b[i.toNat]! then 1
  else if b[i.toNat]! < a[i.toNat]! then 2
  else 0

theorem compareStep_invariant (a b : Array UInt64) (ha : DecimalDigits a) (hb : DecimalDigits b)
    (size : a.size = b.size) (n : Nat) (index : n < a.size) (bound : a.size < UInt64.size)
    (order : UInt64) (invariant : ComparePrefix a b n order) :
    ComparePrefix a b (n + 1) (compareStep a b (UInt64.ofNat n) order) := by
  have indexNat : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' (by omega)
  rcases invariant with ⟨rfl, same⟩ | ⟨rfl, less⟩ | ⟨rfl, greater⟩
  · by_cases less : a[n]! < b[n]!
    · have valueLess := magnitude_lt_of_first a b ha hb size n index same (UInt64.lt_iff_toNat_lt.mp less)
      simpa [ComparePrefix, compareStep, indexNat, less] using valueLess
    · by_cases greater : b[n]! < a[n]!
      · have valueGreater := magnitude_lt_of_first b a hb ha size.symm n (by omega)
          (fun i hi => (same i hi).symm) (UInt64.lt_iff_toNat_lt.mp greater)
        simpa [ComparePrefix, compareStep, indexNat, less, greater] using valueGreater
      · have equal : a[n]! = b[n]! := by
          apply UInt64.toNat.inj
          rw [UInt64.lt_iff_toNat_lt] at less greater
          omega
        simp only [compareStep, bne_self_eq_false, Bool.false_eq_true, ite_false, indexNat,
          less, greater]
        left
        refine ⟨rfl, fun i hi => ?_⟩
        by_cases previous : i < n
        · exact same i previous
        · have current : i = n := by omega
          simpa only [current] using equal
  · simpa [ComparePrefix, compareStep] using less
  · simpa [ComparePrefix, compareStep] using greater

theorem compare_loop_correct (a b : Array UInt64) (ha : DecimalDigits a) (hb : DecimalDigits b)
    (size : a.size = b.size) (bound : a.size < UInt64.size) :
    (LeanExe.loop a.size.toUInt64 0 (compareStep a b) == 1) = decide (magnitude a < magnitude b) := by
  have sizeNat : a.size.toUInt64.toNat = a.size := UInt64.toNat_ofNat_of_lt' bound
  have invariant := LeanExe.Dialect.loop_induction (n := a.size.toUInt64) (init := (0 : UInt64))
    (f := compareStep a b) (ComparePrefix a b) (Or.inl ⟨rfl, by omega⟩)
    (fun n order index before => compareStep_invariant a b ha hb size n (by omega) bound order before)
  rw [sizeNat] at invariant
  rcases invariant with ⟨zero, same⟩ | ⟨one, less⟩ | ⟨two, greater⟩
  · have equal := magnitude_eq_of_digits a b size same
    simp [zero, equal]
  · simp [one, less]
  · simp [two, Nat.not_lt.mpr (Nat.le_of_lt greater)]

end Magnitude

theorem magnitudeLess_correct (a b : Array UInt64) (ha : NormalDigits a) (hb : NormalDigits b)
    (aBound : a.size < UInt64.size) (bBound : b.size < UInt64.size) :
    magnitudeLess a b = decide (magnitude a < magnitude b) := by
  have aNat : a.size.toUInt64.toNat = a.size := UInt64.toNat_ofNat_of_lt' aBound
  have bNat : b.size.toUInt64.toNat = b.size := UInt64.toNat_ofNat_of_lt' bBound
  have sameSizes : a.size.toUInt64 = b.size.toUInt64 ↔ a.size = b.size := by
    constructor
    · intro same
      have := congrArg UInt64.toNat same
      simpa only [aNat, bNat] using this
    · intro same
      rw [same]
  unfold magnitudeLess
  by_cases size : a.size = b.size
  · have wordEq := sameSizes.mpr size
    simp only [wordEq, bne_self_eq_false, Bool.false_eq_true, ite_false]
    have correct := compare_loop_correct a b ha.1 hb.1 size aBound
    change (LeanExe.loop a.size.toUInt64 0 (fun i order =>
      if order != 0 then order
      else if a[i.toNat]! < b[i.toNat]! then 1
      else if b[i.toNat]! < a[i.toNat]! then 2 else 0) == 1) = _ at correct
    simpa only [wordEq] using correct
  · have wordNe : a.size.toUInt64 ≠ b.size.toUInt64 := fun equal => size (sameSizes.mp equal)
    have flag : (a.size.toUInt64 != b.size.toUInt64) = true := by simp [wordNe]
    simp only [flag, ite_true,
      UInt64.lt_iff_toNat_lt, aNat, bNat]
    by_cases less : a.size < b.size
    · simp [less, magnitude_lt_of_size a b ha hb less]
    · have greater := magnitude_lt_of_size b a hb ha (by omega)
      simp [less, Nat.not_lt.mpr (Nat.le_of_lt greater)]

end Demos.RunningSum
