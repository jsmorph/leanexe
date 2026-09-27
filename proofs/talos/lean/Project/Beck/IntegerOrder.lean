import Project.Beck.IntegerAdd

namespace Project.Beck.IntegerOrder

open LeanExe.Examples.BeckExact IntegerAdd

theorem ofWord_correct (word : UInt64) :
    Valid (Integer.ofWord word) ∧ value (Integer.ofWord word) = word.toNat := by
  have low : LimbArithmetic.Valid (word % Digits.radix) := by
    change (word % Digits.radix).toNat < 4294967296
    rw [UInt64.toNat_mod]
    exact Nat.mod_lt _ (by decide)
  have high : LimbArithmetic.Valid (word / Digits.radix) := by
    have bound := word.toNat_lt
    change (word / Digits.radix).toNat < 4294967296
    rw [UInt64.toNat_div]
    change word.toNat / 4294967296 < 4294967296
    omega
  refine ⟨make_valid false _ ?_, ?_⟩
  · intro digit member
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact low
    · exact high
  · rw [Integer.ofWord, make_value]
    simp only [Bool.false_eq_true, ite_false, DigitValue.value,
      List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero,
      UInt64.toNat_mod, UInt64.toNat_div]
    change (↑(word.toNat % 4294967296 + 4294967296 * (word.toNat / 4294967296)) : ℤ) = _
    rw [Nat.mod_add_div]

theorem abs_correct (a : Integer) (ha : Valid a) :
    Valid (Integer.abs a) ∧ value (Integer.abs a) = |value a| := by
  refine ⟨⟨ha.1, by simp [Integer.abs]⟩, ?_⟩
  cases sign : a.negative <;> simp [Integer.abs, value, sign]

theorem equal_correct (a b : Integer) (ha : Valid a) (hb : Valid b) :
    Integer.equal a b = true ↔ value a = value b := by
  have zeroA := ha.2
  have zeroB := hb.2
  rw [Integer.equal, DigitCompare.compare_correct _ _ ha.1 hb.1]
  by_cases ab : DigitValue.value a.digits < DigitValue.value b.digits <;>
    by_cases ba : DigitValue.value b.digits < DigitValue.value a.digits <;>
    simp only [ab, ba, ite_true, ite_false] <;>
    cases signA : a.negative <;> cases signB : b.negative <;>
    simp_all [value] <;> omega

theorem less_correct (a b : Integer) (ha : Valid a) (hb : Valid b) :
    Integer.less a b = true ↔ value a < value b := by
  have zeroA := ha.2
  have zeroB := hb.2
  rw [Integer.less, DigitCompare.compare_correct _ _ ha.1 hb.1]
  by_cases ab : DigitValue.value a.digits < DigitValue.value b.digits <;>
    by_cases ba : DigitValue.value b.digits < DigitValue.value a.digits <;>
    simp only [ab, ba, ite_true, ite_false] <;>
    cases signA : a.negative <;> cases signB : b.negative <;>
    simp_all [value] <;> omega

#print axioms ofWord_correct
#print axioms equal_correct
#print axioms less_correct

end Project.Beck.IntegerOrder
