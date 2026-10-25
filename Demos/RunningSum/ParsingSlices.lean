import Demos.RunningSum.Magnitude

namespace Demos.RunningSum

theorem extract_byte (input : Array UInt64) (start stop i : Nat)
    (hs : stop ≤ input.size) (hi : i < stop - start) :
    (input.extract start stop)[i]! = input[start + i]! := by
  rw [getElem!_pos (input.extract start stop) i (by
    simp only [Array.size_extract, Nat.min_eq_left hs]
    exact hi), getElem!_pos input (start + i) (by omega), Array.getElem_extract]

theorem extract_valid (input : Array UInt64) (start stop : Nat) (hs : stop ≤ input.size)
    (h : ∀ i, start ≤ i → i < stop → 48 ≤ input[i]!.toNat ∧ input[i]!.toNat ≤ 57) :
    DecimalDigits (input.extract start stop) := by
  intro i hi
  simp only [Array.size_extract, Nat.min_eq_left hs] at hi
  rw [extract_byte input start stop i hs hi]
  exact h (start + i) (by omega) (by omega)

theorem lowValue_congr (a b : Array UInt64) (n : Nat)
    (h : ∀ i, i < n → Magnitude.digit a i = Magnitude.digit b i) :
    Magnitude.lowValue a n = Magnitude.lowValue b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Magnitude.lowValue, Magnitude.lowValue, ih (fun i hi => h i (by omega)),
        h n (by omega)]

theorem extract_digit (input : Array UInt64) (start stop i : Nat)
    (hs : stop ≤ input.size) (hi : i < stop - start) :
    Magnitude.digit (input.extract start stop) i = digitValue input[stop - 1 - i]! := by
  simp only [Magnitude.digit, Array.size_extract, Nat.min_eq_left hs, hi, ite_true]
  rw [extract_byte input start stop _ hs (by omega)]
  rw [show start + (stop - start - 1 - i) = stop - 1 - i by omega]

theorem drop_leading_zeros (input : Array UInt64) (start first stop : Nat)
    (hstart : start ≤ first) (hfirst : first ≤ stop) (hstop : stop ≤ input.size)
    (hzero : ∀ i, start ≤ i → i < first → input[i]! = 48) :
    magnitude (input.extract first stop) = magnitude (input.extract start stop) := by
  have he : Magnitude.lowValue (input.extract first stop) (stop - start) =
      Magnitude.lowValue (input.extract start stop) (stop - start) := by
    apply lowValue_congr
    intro i hi
    rw [extract_digit input start stop i hstop hi]
    by_cases inside : i < stop - first
    · rw [extract_digit input first stop i hstop inside]
    · simp only [Magnitude.digit, Array.size_extract, Nat.min_eq_left hstop,
        inside, ite_false]
      rw [hzero (stop - 1 - i) (by omega) (by omega)]
      rfl
  rw [Magnitude.lowValue_stable _ _ (by
    simp only [Array.size_extract, Nat.min_eq_left hstop]
    omega), Magnitude.lowValue_stable _ _ (by
    simp only [Array.size_extract, Nat.min_eq_left hstop]
    omega)] at he
  exact he

end Demos.RunningSum
