import Demos.RunningSum.MagnitudeNormalize

namespace Demos.RunningSum

open Magnitude

theorem combineMagnitude_eq (a b : Array UInt64) (subtract : Bool)
    (bound : max a.size b.size + 1 < UInt64.size) :
    combineMagnitude a b subtract =
      let state := digitPrefix a b subtract (max a.size b.size)
      finishDigits (if !subtract && state.2 != 0 then state.1.push state.2 else state.1) := by
  have aBound : a.size < UInt64.size := by omega
  have bBound : b.size < UInt64.size := by omega
  have aNat : a.size.toUInt64.toNat = a.size := UInt64.toNat_ofNat_of_lt' aBound
  have bNat : b.size.toUInt64.toNat = b.size := UInt64.toNat_ofNat_of_lt' bBound
  have countNat : (max a.size.toUInt64 b.size.toUInt64).toNat = max a.size b.size := by
    change (if a.size.toUInt64 ≤ b.size.toUInt64 then b.size.toUInt64 else a.size.toUInt64).toNat = _
    by_cases less : a.size ≤ b.size
    · have wordLe : a.size.toUInt64 ≤ b.size.toUInt64 :=
        UInt64.le_iff_toNat_le.mpr (by rw [aNat, bNat]; exact less)
      simp only [wordLe, ite_true, bNat, max_eq_right less]
    · have wordNot : ¬a.size.toUInt64 ≤ b.size.toUInt64 := by
        simpa only [UInt64.le_iff_toNat_le, aNat, bNat] using less
      simp only [wordNot, ite_false, aNat, max_eq_left (by omega : b.size ≤ a.size)]
  unfold combineMagnitude
  dsimp only
  rw [digitPrefix_loop a b subtract (max a.size.toUInt64 b.size.toUInt64) aBound bBound, countNat]
  let state := digitPrefix a b subtract (max a.size b.size)
  let raw := if !subtract && state.2 != 0 then state.1.push state.2 else state.1
  have rawSize : raw.size ≤ max a.size b.size + 1 := by
    dsimp only [raw, state]
    split <;> simp only [Array.size_push, digitPrefix_size] <;> omega
  have rawBound : raw.size < UInt64.size := lt_of_le_of_lt rawSize bound
  let trimmed : UInt64 := LeanExe.repeatWhile raw.size.toUInt64 raw.size.toUInt64
    (fun size => size > 0 && raw[(size - 1).toNat]! == 0) (fun size => size - 1)
  change (LeanExe.build trimmed fun i => raw[(trimmed - 1 - i).toNat]! + 48) = finishDigits raw
  rw [show trimmed = (trimSize raw raw.size).toUInt64 from trimSize_repeat raw rawBound]
  rfl

theorem combine_add (a b : Array UInt64) (ha : DecimalDigits a) (hb : DecimalDigits b)
    (bound : max a.size b.size + 1 < UInt64.size) :
    NormalDigits (combineMagnitude a b false) ∧
      magnitude (combineMagnitude a b false) = magnitude a + magnitude b ∧
      (combineMagnitude a b false).size ≤ max a.size b.size + 1 := by
  have invariant := digitPrefix_invariant a b ha hb false (max a.size b.size)
  rw [combineMagnitude_eq a b false bound]
  generalize stateEq : digitPrefix a b false (max a.size b.size) = state at *
  obtain ⟨size, digits, carry, value⟩ := invariant
  simp only [Bool.false_eq_true, ite_false] at value
  rw [lowValue_stable a _ (le_max_left _ _), lowValue_stable b _ (le_max_right _ _)] at value
  by_cases zero : state.2 = 0
  · simp only [Bool.not_false, Bool.true_and, zero, bne_self_eq_false, Bool.false_eq_true, ite_false]
    obtain ⟨normal, resultValue, resultSize⟩ := finishDigits_spec state.1 digits (by omega)
    refine ⟨normal, ?_, by omega⟩
    rw [resultValue]
    simpa [zero] using value
  · have flag : (state.2 != 0) = true := by simp [zero]
    simp only [Bool.not_false, Bool.true_and, flag, ite_true]
    have rawDigits := rawDigits_push state.1 state.2 digits (by omega)
    obtain ⟨normal, resultValue, resultSize⟩ := finishDigits_spec _ rawDigits (by
      simp only [Array.size_push]
      omega)
    refine ⟨normal, ?_, by simpa only [Array.size_push, size] using resultSize⟩
    rw [resultValue, rawValue_push, size]
    exact value

theorem combine_sub (a b : Array UInt64) (ha : DecimalDigits a) (hb : DecimalDigits b)
    (bound : max a.size b.size + 1 < UInt64.size) (less : magnitude b ≤ magnitude a) :
    NormalDigits (combineMagnitude a b true) ∧
      magnitude (combineMagnitude a b true) = magnitude a - magnitude b ∧
      (combineMagnitude a b true).size ≤ max a.size b.size + 1 := by
  have invariant := digitPrefix_invariant a b ha hb true (max a.size b.size)
  rw [combineMagnitude_eq a b true bound]
  generalize stateEq : digitPrefix a b true (max a.size b.size) = state at *
  obtain ⟨size, digits, carry, value⟩ := invariant
  simp only [ite_true] at value
  rw [lowValue_stable a _ (le_max_left _ _), lowValue_stable b _ (le_max_right _ _)] at value
  have rawBound := rawValue_lt state.1 digits
  rw [size] at rawBound
  have noBorrow : state.2.toNat = 0 := by
    by_contra nonzero
    have one : state.2.toNat = 1 := by omega
    rw [one, one_mul] at value
    omega
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
  obtain ⟨normal, resultValue, resultSize⟩ := finishDigits_spec state.1 digits (by omega)
  refine ⟨normal, ?_, by omega⟩
  rw [resultValue]
  rw [noBorrow, zero_mul, add_zero] at value
  omega

end Demos.RunningSum
