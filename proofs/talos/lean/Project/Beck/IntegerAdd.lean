import Project.Beck.DigitCompare
import Project.Beck.DigitSub

namespace Project.Beck.IntegerAdd

open LeanExe.Examples.BeckExact

def value (integer : Integer) : ℤ :=
  if integer.negative then -(DigitValue.value integer.digits : ℤ) else DigitValue.value integer.digits

def Valid (integer : Integer) : Prop :=
  DigitValue.Valid integer.digits ∧ (DigitValue.value integer.digits = 0 → integer.negative = false)

theorem length_zero_iff (digits : Array UInt64) :
    Digits.length digits = 0 ↔ DigitValue.value digits = 0 := by
  constructor
  · intro zero
    rw [← DigitValue.trim_value digits]
    simp [Digits.trim, zero, DigitValue.value]
  · intro zero
    by_contra nonzero
    have lower := DigitCompare.value_lower_bound digits (by omega)
    have positive : 0 < (4294967296 : ℕ) ^ (Digits.length digits - 1) := by positivity
    omega

theorem trim_size (digits : Array UInt64) : (Digits.trim digits).size = Digits.length digits := by
  simp [Digits.trim, Array.size_extract, Nat.min_eq_left (DigitValue.length_le digits)]

theorem make_value (negative : Bool) (digits : Array UInt64) :
    value (Integer.make negative digits) =
      if negative then -(DigitValue.value digits : ℤ) else DigitValue.value digits := by
  by_cases zero : DigitValue.value digits = 0
  · simp [value, Integer.make, DigitValue.trim_value, zero]
  · have positive : Digits.length digits ≠ 0 := mt (length_zero_iff digits).mp zero
    simp [value, Integer.make, DigitValue.trim_value, trim_size, positive]

theorem make_valid (negative : Bool) (digits : Array UInt64) (valid : DigitValue.Valid digits) :
    Valid (Integer.make negative digits) := by
  refine ⟨DigitValue.trim_valid digits valid, ?_⟩
  intro zero
  have length : Digits.length digits = 0 := (length_zero_iff digits).mpr
    (by simpa [Integer.make, DigitValue.trim_value] using zero)
  simp [Integer.make, trim_size, length]

theorem zero_correct : Valid Integer.zero ∧ value Integer.zero = 0 := by
  simp [Valid, value, Integer.zero, DigitValue.Valid, DigitValue.value]

theorem isZero_correct (integer : Integer) : Integer.isZero integer = true ↔ value integer = 0 := by
  simp only [Integer.isZero, beq_iff_eq, length_zero_iff, value]
  cases integer.negative <;> simp

theorem neg_correct (integer : Integer) (valid : Valid integer) :
    Valid (Integer.neg integer) ∧ value (Integer.neg integer) = -value integer := by
  refine ⟨make_valid _ _ valid.1, ?_⟩
  rw [Integer.neg, make_value]
  cases sign : integer.negative <;> simp [value, sign]

theorem add_correct (a b : Integer) (ha : Valid a) (hb : Valid b) :
    Valid (Integer.add a b) ∧ value (Integer.add a b) = value a + value b := by
  by_cases same : a.negative = b.negative
  · have source : Integer.add a b = Integer.make a.negative (Digits.add a.digits b.digits) := by
      simp [Integer.add, same]
    rw [source]
    refine ⟨make_valid _ _ (DigitAdd.add_valid _ _ ha.1 hb.1), ?_⟩
    rw [make_value, DigitAdd.add_value _ _ ha.1 hb.1]
    cases sign : b.negative <;> simp [value, same, sign, add_comm]
  · by_cases smaller : DigitValue.value a.digits < DigitValue.value b.digits
    · have source : Integer.add a b = Integer.make b.negative (Digits.sub b.digits a.digits) := by
        simp [Integer.add, same, DigitCompare.compare_correct _ _ ha.1 hb.1, smaller]
      have sub := DigitSub.sub_correct b.digits a.digits hb.1 ha.1 (by omega)
      rw [source]
      refine ⟨make_valid _ _ sub.1, ?_⟩
      rw [make_value, sub.2, Int.ofNat_sub (by omega)]
      cases signA : a.negative <;> cases signB : b.negative <;>
        simp_all [value] <;> omega
    · have source : Integer.add a b = Integer.make a.negative (Digits.sub a.digits b.digits) := by
        simp only [Integer.add, beq_iff_eq, same, ite_false,
          DigitCompare.compare_correct _ _ ha.1 hb.1, smaller]
        split <;> simp
      have sub := DigitSub.sub_correct a.digits b.digits ha.1 hb.1 (by omega)
      rw [source]
      refine ⟨make_valid _ _ sub.1, ?_⟩
      rw [make_value, sub.2, Int.ofNat_sub (by omega)]
      cases signA : a.negative <;> cases signB : b.negative <;>
        simp_all [value] <;> omega

theorem sub_correct (a b : Integer) (ha : Valid a) (hb : Valid b) :
    Valid (Integer.sub a b) ∧ value (Integer.sub a b) = value a - value b := by
  have neg := neg_correct b hb
  have sum := add_correct a (Integer.neg b) ha neg.1
  simpa [Integer.sub, neg.2, sub_eq_add_neg] using sum

#print axioms add_correct
#print axioms sub_correct

end Project.Beck.IntegerAdd
