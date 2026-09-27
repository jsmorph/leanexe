import Project.Beck.DigitAdd

namespace Project.Beck.DigitUpdate

open LeanExe.Examples.BeckExact DigitValue

theorem list_set_value (digits : List UInt64) (index : ℕ) (digit : UInt64)
    (inside : index < digits.length) :
    Nat.ofDigits 4294967296 ((digits.set index digit).map UInt64.toNat) +
        4294967296 ^ index * digits[index].toNat =
      Nat.ofDigits 4294967296 (digits.map UInt64.toNat) + 4294967296 ^ index * digit.toNat := by
  induction digits generalizing index with
  | nil => simp at inside
  | cons head tail ih =>
    cases index with
    | zero => simp [Nat.ofDigits_cons]; omega
    | succ index =>
      have prior := ih index (by simpa using inside)
      simp only [List.set_cons_succ, List.map_cons, Nat.ofDigits_cons,
        List.getElem_cons_succ, pow_succ]
      nlinarith

theorem value_set (digits : Array UInt64) (index : ℕ) (digit : UInt64)
    (inside : index < digits.size) :
    value (digits.set! index digit) + 4294967296 ^ index * digits[index]!.toNat =
      value digits + 4294967296 ^ index * digit.toNat := by
  have result := list_set_value digits.toList index digit (by simpa using inside)
  rw [Array.getElem_toList] at result
  simpa only [value, Array.toList_set!, getElem!_pos digits index inside] using result

theorem valid_set (digits : Array UInt64) (valid : Valid digits) (index : ℕ)
    (digit : UInt64) (digitValid : LimbArithmetic.Valid digit) : Valid (digits.set! index digit) := by
  intro word member
  rcases Array.mem_or_eq_of_mem_setIfInBounds member with prior | equal
  · exact valid word prior
  · simpa [equal] using digitValid

theorem valid_get (digits : Array UInt64) (valid : Valid digits) (index : ℕ)
    (inside : index < digits.size) : LimbArithmetic.Valid digits[index]! := by
  rw [getElem!_pos digits index inside]
  exact valid _ (Array.getElem_mem inside)

theorem value_zeros (count : ℕ) : value (Array.replicate count (0 : UInt64)) = 0 := by
  simp [value, List.map_replicate, Nat.ofDigits_replicate_zero]

theorem valid_zeros (count : ℕ) : Valid (Array.replicate count (0 : UInt64)) := by
  intro digit member
  have equal : digit = 0 := (Array.mem_replicate.mp member).2
  subst digit
  exact (by decide : (0 : UInt64).toNat < 4294967296)

#print axioms value_set

end Project.Beck.DigitUpdate
