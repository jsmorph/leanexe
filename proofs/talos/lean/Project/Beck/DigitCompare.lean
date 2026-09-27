import Project.Beck.DigitAdd

namespace Project.Beck.DigitCompare

open LeanExe.Examples.BeckExact DigitValue DigitAdd

theorem lowerValue_bound (a : Array UInt64) (valid : Valid a) (count : ℕ)
    (inside : count ≤ a.size) : lowerValue a count < 4294967296 ^ count := by
  have bound := value_bound (a.extract 0 count) (extract_valid a valid 0 count)
  simpa [lowerValue, Array.size_extract, Nat.min_eq_left inside] using bound

theorem block_lt (power a b lowA lowB : ℕ) (ha : lowA < power) (_hb : lowB < power)
    (ordered : a < b) : lowA + power * a < lowB + power * b := by
  have scaled := Nat.mul_le_mul_left power (Nat.succ_le_of_lt ordered)
  nlinarith

theorem compareFrom_correct (a b : Array UInt64) (ha : Valid a) (hb : Valid b)
    (count : ℕ) (ia : count ≤ a.size) (ib : count ≤ b.size) :
    Digits.compareFrom count a b =
      if lowerValue a count < lowerValue b count then 1
      else if lowerValue b count < lowerValue a count then 2 else 0 := by
  induction count with
  | zero => simp [Digits.compareFrom, lowerValue, value]
  | succ count ih =>
    have insideA : count < a.size := by omega
    have insideB : count < b.size := by omega
    have boundA := lowerValue_bound a ha count (by omega)
    have boundB := lowerValue_bound b hb count (by omega)
    have nextA : lowerValue a (count + 1) = lowerValue a count +
        4294967296 ^ count * a[count]!.toNat := by
      simpa [Digits.get, insideA] using prefix_next a count
    have nextB : lowerValue b (count + 1) = lowerValue b count +
        4294967296 ^ count * b[count]!.toNat := by
      simpa [Digits.get, insideB] using prefix_next b count
    by_cases smaller : a[count]!.toNat < b[count]!.toNat
    · have whole : lowerValue a (count + 1) < lowerValue b (count + 1) := by
        rw [nextA, nextB]
        exact block_lt _ _ _ _ _ boundA boundB smaller
      simp [Digits.compareFrom, UInt64.lt_iff_toNat_lt, smaller, whole]
    · by_cases larger : b[count]!.toNat < a[count]!.toNat
      · have whole : lowerValue b (count + 1) < lowerValue a (count + 1) := by
          rw [nextA, nextB]
          exact block_lt _ _ _ _ _ boundB boundA larger
        have reverse : ¬lowerValue a (count + 1) < lowerValue b (count + 1) := by omega
        simp [Digits.compareFrom, UInt64.lt_iff_toNat_lt, smaller, larger, whole, reverse]
      · have equal : a[count]!.toNat = b[count]!.toNat := by omega
        simp only [Digits.compareFrom, UInt64.lt_iff_toNat_lt, nextA, nextB, equal, Nat.lt_irrefl, ite_false, Nat.add_lt_add_iff_right]
        exact ih (by omega) (by omega)

theorem lengthFrom_last (a : Array UInt64) (count : ℕ)
    (positive : 0 < Digits.lengthFrom count a) :
    a[Digits.lengthFrom count a - 1]! ≠ 0 := by
  induction count with
  | zero => simp [Digits.lengthFrom] at positive
  | succ count ih =>
    simp only [Digits.lengthFrom] at positive ⊢
    split
    · rename_i nonzero
      simpa using nonzero
    · rename_i zero
      exact ih (by simpa [zero] using positive)

theorem value_at_length (a : Array UInt64) : lowerValue a (Digits.length a) = value a :=
  trim_value a

theorem value_lower_bound (a : Array UInt64) (positive : 0 < Digits.length a) :
    4294967296 ^ (Digits.length a - 1) ≤ value a := by
  have nonzero := lengthFrom_last a a.size positive
  have nonzeroNat : a[Digits.length a - 1]!.toNat ≠ 0 := by
    intro zero
    apply nonzero
    apply UInt64.toNat_inj.mp
    simpa [Digits.length] using zero
  have indexBound : Digits.length a - 1 < a.size := by
    have size := length_le a
    omega
  have last := prefix_next a (Digits.length a - 1)
  have size : Digits.length a - 1 + 1 = Digits.length a := by omega
  rw [size, value_at_length] at last
  simp only [Digits.get, indexBound, ite_true] at last
  have scaled := Nat.mul_le_mul_left (4294967296 ^ (Digits.length a - 1))
    (Nat.one_le_iff_ne_zero.mpr nonzeroNat)
  simp only [mul_one] at scaled
  omega

theorem value_upper_bound (a : Array UInt64) (valid : Valid a) :
    value a < 4294967296 ^ Digits.length a := by
  rw [← value_at_length]
  exact lowerValue_bound a valid _ (length_le a)

theorem shorter (a b : Array UInt64) (valid : Valid a)
    (lengths : Digits.length a < Digits.length b) : value a < value b := by
  have lower := value_lower_bound b (by omega)
  have upper := value_upper_bound a valid
  have powers : 4294967296 ^ Digits.length a ≤ 4294967296 ^ (Digits.length b - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem compare_correct (a b : Array UInt64) (ha : Valid a) (hb : Valid b) :
    Digits.compare a b =
      if value a < value b then 1 else if value b < value a then 2 else 0 := by
  by_cases smaller : Digits.length a < Digits.length b
  · simp [Digits.compare, smaller, shorter a b ha smaller]
  · by_cases larger : Digits.length b < Digits.length a
    · have whole := shorter b a hb larger
      have reverse : ¬value a < value b := by omega
      simp [Digits.compare, smaller, larger, whole, reverse]
    · have equal : Digits.length a = Digits.length b := by omega
      have result := compareFrom_correct a b ha hb (Digits.length a) (length_le a)
        (by rw [equal]; exact length_le b)
      rw [value_at_length a, equal, value_at_length b] at result
      simpa [Digits.compare, smaller, larger, equal] using result

#print axioms compare_correct

end Project.Beck.DigitCompare
