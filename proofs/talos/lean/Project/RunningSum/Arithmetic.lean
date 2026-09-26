import Project.RunningSum.Reverse

namespace Project.RunningSum

open LeanExe.Examples.RunningSum (combineMagnitude)

theorem combine_add (a b : ByteArray) (ha : AsciiDigits a) (hb : AsciiDigits b) :
    Canonical (combineMagnitude a b false) ∧
    magnitude (combineMagnitude a b false) = magnitude a + magnitude b := by
  have hinv := digitPrefix_invariant a b ha hb false (max a.size b.size)
  rw [combineMagnitude_eq]
  generalize hs : digitPrefix a b false (max a.size b.size) = state at *
  obtain ⟨hsize, hdigits, hcarry, hvalue⟩ := hinv
  simp only [Bool.false_eq_true, ite_false] at hvalue
  rw [lowValue_stable a _ (le_max_left _ _), lowValue_stable b _ (le_max_right _ _)] at hvalue
  by_cases hc : state.2 = 0
  · simp only [Bool.not_false, Bool.true_and, hc, bne_self_eq_false, Bool.false_eq_true, ite_false]
    obtain ⟨hcanon, hnat⟩ := finishDigits_spec state.1 hdigits
    refine ⟨hcanon, ?_⟩
    simpa [hnat, hc] using hvalue
  · have hflag : (state.2 != 0) = true := by simp [hc]
    simp only [Bool.not_false, Bool.true_and, hflag, ite_true]
    have hcByte : state.2.toUInt8.toNat = state.2.toNat := by
      rw [UInt64.toNat_toUInt8, Nat.mod_eq_of_lt (by omega)]
    have hnew := rawDigits_push state.1 state.2.toUInt8 hdigits (by rw [hcByte]; omega)
    obtain ⟨hcanon, hnat⟩ := finishDigits_spec _ hnew
    refine ⟨hcanon, ?_⟩
    rw [hnat, rawValue_push, hcByte, hsize]
    exact hvalue

theorem combine_sub (a b : ByteArray) (ha : AsciiDigits a) (hb : AsciiDigits b)
    (hle : magnitude b ≤ magnitude a) :
    Canonical (combineMagnitude a b true) ∧
    magnitude (combineMagnitude a b true) = magnitude a - magnitude b := by
  have hinv := digitPrefix_invariant a b ha hb true (max a.size b.size)
  rw [combineMagnitude_eq]
  generalize hs : digitPrefix a b true (max a.size b.size) = state at *
  obtain ⟨hsize, hdigits, hcarry, hvalue⟩ := hinv
  simp only [ite_true] at hvalue
  rw [lowValue_stable a _ (le_max_left _ _), lowValue_stable b _ (le_max_right _ _)] at hvalue
  have hraw := rawValue_lt state.1 hdigits
  rw [hsize] at hraw
  have hc : state.2.toNat = 0 := by
    by_contra hnonzero
    have hone : state.2.toNat = 1 := by omega
    rw [hone, one_mul] at hvalue
    omega
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
  obtain ⟨hcanon, hnat⟩ := finishDigits_spec state.1 hdigits
  refine ⟨hcanon, ?_⟩
  rw [hnat]
  rw [hc, zero_mul, add_zero] at hvalue
  omega

#print axioms combine_add
#print axioms combine_sub

end Project.RunningSum
