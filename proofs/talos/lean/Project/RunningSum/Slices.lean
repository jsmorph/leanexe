import Project.RunningSum.Add

namespace Project.RunningSum

theorem extract_byte (bytes : ByteArray) (start stop i : Nat)
    (hs : stop ≤ bytes.size) (hi : i < stop - start) :
    (bytes.extract start stop)[i]! = bytes[start + i]! := by
  rw [getElem!_pos _ _ (by simp only [ByteArray.size_extract, Nat.min_eq_left hs]; exact hi)]
  rw [getElem!_pos _ _ (by omega)]
  simp [ByteArray.getElem_eq_getElem_data, ByteArray.data_extract]

theorem extract_valid (bytes : ByteArray) (start stop : Nat) (hs : stop ≤ bytes.size)
    (h : ∀ i, start ≤ i → i < stop → 48 ≤ bytes[i]!.toNat ∧ bytes[i]!.toNat ≤ 57) :
    AsciiDigits (bytes.extract start stop) := by
  intro i hi
  simp only [ByteArray.size_extract, Nat.min_eq_left hs] at hi
  rw [extract_byte bytes start stop i hs hi]
  exact h (start + i) (by omega) (by omega)

theorem lowValue_congr (a b : ByteArray) (n : Nat)
    (h : ∀ i, i < n → digit a i = digit b i) : lowValue a n = lowValue b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [lowValue, lowValue, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem extract_digit (bytes : ByteArray) (start stop i : Nat)
    (hs : stop ≤ bytes.size) (hi : i < stop - start) :
    digit (bytes.extract start stop) i = bytes[stop - 1 - i]!.toNat - 48 := by
  simp only [digit, ByteArray.size_extract, Nat.min_eq_left hs, hi, ite_true]
  rw [extract_byte bytes start stop _ hs (by omega)]
  rw [show start + (stop - start - 1 - i) = stop - 1 - i by omega]

theorem drop_leading_zeros (bytes : ByteArray) (start first stop : Nat)
    (hstart : start ≤ first) (hfirst : first ≤ stop) (hstop : stop ≤ bytes.size)
    (hzero : ∀ i, start ≤ i → i < first → bytes[i]! = 48) :
    magnitude (bytes.extract first stop) = magnitude (bytes.extract start stop) := by
  have he : lowValue (bytes.extract first stop) (stop - start) =
      lowValue (bytes.extract start stop) (stop - start) := by
    apply lowValue_congr
    intro i hi
    rw [extract_digit bytes start stop i hstop hi]
    by_cases hlt : i < stop - first
    · rw [extract_digit bytes first stop i hstop hlt]
    · simp only [digit, ByteArray.size_extract, Nat.min_eq_left hstop, hlt, ite_false]
      rw [hzero (stop - 1 - i) (by omega) (by omega)]
      rfl
  rw [lowValue_stable _ _ (by simp only [ByteArray.size_extract, Nat.min_eq_left hstop]; omega)] at he
  simpa only [magnitude, ByteArray.size_extract, Nat.min_eq_left hstop] using he

end Project.RunningSum
