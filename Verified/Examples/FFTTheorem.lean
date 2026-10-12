import Verified.Examples.FFTNumerical

namespace Verified.Examples.FFTTheorem

open CodeLib.IEEE64 LeanExe.ProofKit.F64Approx FFTSpec

theorem nWord_eq (xs : Array Float) (hn : xs.size / 2 ≤ 2 ^ 32) :
    xs.size.toUInt64 / 2 = UInt64.ofNat (xs.size / 2) := by
  have h : (xs.size.toUInt64 / 2).toNat = xs.size / 2 := FourierLoop.nWord_toNat xs hn
  rw [← h, UInt64.ofNat_toNat]

theorem magnitudeBound_eq (xs : Array Float) :
    magnitudeBound xs = FourierSpec.inputNorm xs + errorBound xs := by
  unfold magnitudeBound errorBound
  split
  · unfold radixMagnitude radixError
    ring
  · exact FourierSpec.magnitudeBound_eq_inputNorm_add_errorBound xs

theorem errorBound_nonneg (xs : Array Float) : 0 ≤ errorBound xs := by
  unfold errorBound
  split
  · exact FFTNumerical.radixError_nonneg _ _ (FourierSpec.inputNorm_nonneg xs)
  · exact FourierSpec.errorBound_nonneg xs

theorem magnitudeBound_nonneg (xs : Array Float) : 0 ≤ magnitudeBound xs := by
  rw [magnitudeBound_eq]
  exact add_nonneg (FourierSpec.inputNorm_nonneg xs) (errorBound_nonneg xs)

theorem magnitude_safe (xs : Array Float) (h : Admissible xs) :
    magnitudeBound xs < (2 : ℝ) ^ 1022 := by
  unfold magnitudeBound
  split
  · rename_i hr
    have hs := h.2.2
    rw [ite_eq_left hr] at hs
    unfold radixSafety at hs
    have hM := FFTNumerical.radixMagnitude_nonneg (Nat.log2 (xs.size / 2))
      (FourierSpec.inputNorm xs) (FourierSpec.inputNorm_nonneg xs)
    have hq := mul_le_mul_of_nonneg_right FFTArithmetic.q_ge_one hM
    have he := mul_nonneg (by linarith [FFTArithmetic.unit_nonneg] :
      (0 : ℝ) ≤ 2 * (1 + unitRoundoff64)) FFTArithmetic.eta_nonneg
    have hmq := show radixMagnitude (Nat.log2 (xs.size / 2)) (FourierSpec.inputNorm xs) ≤
        FFTArithmetic.q * radixMagnitude (Nat.log2 (xs.size / 2)) (FourierSpec.inputNorm xs) by
      simpa only [one_mul] using hq
    have hq0 := hM.trans hmq
    have hscale := le_mul_of_one_le_left hq0 (by norm_num : (1 : ℝ) ≤ 2)
    have hbound := (hmq.trans hscale).trans (le_add_of_nonneg_right he)
    rw [mul_assoc] at hs
    exact hbound.trans_lt hs
  · rename_i hr
    have hs := h.2.2
    rwa [ite_eq_right hr] at hs

theorem radix2_admissible (xs : Array Float) (h : Admissible xs)
    (hr : FFT.isRadix2 (UInt64.ofNat (xs.size / 2)) = true) :
    Radix2Admissible xs (Nat.log2 (xs.size / 2)) := by
  have hn : (UInt64.ofNat (xs.size / 2)).toNat = xs.size / 2 :=
    UInt64.toNat_ofNat_of_lt' (h.1.trans_lt (by norm_num [UInt64.size]))
  obtain ⟨p, hp, hnP⟩ := (FFTBits.isRadix2_iff_bounded
    (UInt64.ofNat (xs.size / 2)) (by rw [hn]; exact h.1)).mp hr
  rw [hn] at hnP
  have hlog : Nat.log2 (xs.size / 2) = p := by rw [hnP, Nat.log2_two_pow]
  refine ⟨by rw [hlog]; exact hnP, by rw [hlog]; exact hp, h.2.1, ?_⟩
  have hs := h.2.2
  rwa [ite_eq_left hr] at hs

theorem fallback_admissible (xs : Array Float) (h : Admissible xs)
    (hr : FFT.isRadix2 (UInt64.ofNat (xs.size / 2)) = false) : FourierSpec.Admissible xs := by
  refine ⟨h.1, h.2.1, ?_⟩
  have hs := h.2.2
  simpa only [hr, Bool.false_eq_true, ite_false] using hs

theorem transform_accuracy (xs : Array Float) (inverse : Bool) (h : Admissible xs) :
    let ys := FFT.fftTransformWith Trig.invPi Trig.halfPi (FFTNumerical.direction inverse) xs
    ys.size = 2 * (xs.size / 2) ∧ ∀ k, k < xs.size / 2 →
      FApprox ys[2 * k]!
        (if inverse then FourierPositive.realReference xs k else FourierSpec.realDFT xs k)
        (errorBound xs) ∧
      FApprox ys[2 * k + 1]!
        (if inverse then FourierPositive.imagReference xs k else FourierSpec.imagDFT xs k)
        (errorBound xs) ∧
      |value ys[2 * k]!.toBits| ≤ magnitudeBound xs ∧
      |value ys[2 * k + 1]!.toBits| ≤ magnitudeBound xs := by
  by_cases hr : FFT.isRadix2 (UInt64.ofNat (xs.size / 2)) = true
  · have ha := FFTNumerical.radix2_accuracy xs inverse (Nat.log2 (xs.size / 2))
      (radix2_admissible xs h hr)
    simpa only [FFT.fftTransformWith, nWord_eq xs h.1, hr, ite_true,
      errorBound, magnitudeBound] using ha
  · have hrfalse : FFT.isRadix2 (UInt64.ofNat (xs.size / 2)) = false :=
      Bool.eq_false_of_not_eq_true hr
    have hadm := fallback_admissible xs h hrfalse
    dsimp only
    rw [FFTLoop.fftTransformWith_eq_fourier _ _ _ xs (by rw [nWord_eq xs h.1]; exact hrfalse)]
    simp only [errorBound, magnitudeBound, hrfalse, Bool.false_eq_true, ite_false]
    cases inverse with
    | false =>
      have ha := FourierTheorem.dft_accuracy xs hadm
      refine ⟨ha.1, ?_⟩
      intro k hk
      have row := ha.2 k hk
      have hre : FApprox (Fourier.dft xs)[2 * k]! (FourierSpec.realDFT xs k)
          (FourierSpec.errorBound xs) := ⟨row.1, row.2.2.1⟩
      have him : FApprox (Fourier.dft xs)[2 * k + 1]! (FourierSpec.imagDFT xs k)
          (FourierSpec.errorBound xs) := ⟨row.2.1, row.2.2.2⟩
      refine ⟨hre, him, ?_, ?_⟩
      · rw [FourierSpec.magnitudeBound_eq_inputNorm_add_errorBound]
        exact hre.mag.trans (add_le_add (FourierSpec.realDFT_abs_le_inputNorm xs k) le_rfl)
      · rw [FourierSpec.magnitudeBound_eq_inputNorm_add_errorBound]
        exact him.mag.trans (add_le_add (FourierSpec.imagDFT_abs_le_inputNorm xs k) le_rfl)
    | true =>
      have ha := FourierPositive.accuracy xs hadm
      refine ⟨ha.1, ?_⟩
      intro k hk
      obtain ⟨hre, him⟩ := ha.2 k hk
      refine ⟨hre, him, ?_, ?_⟩
      · rw [FourierSpec.magnitudeBound_eq_inputNorm_add_errorBound]
        exact hre.mag.trans (add_le_add (FourierPositive.realReference_abs xs k) le_rfl)
      · rw [FourierSpec.magnitudeBound_eq_inputNorm_add_errorBound]
        exact him.mag.trans (add_le_add (FourierPositive.imagReference_abs xs k) le_rfl)

theorem fft_accuracy (xs : Array Float) (h : Admissible xs) :
    AccurateOutput xs (FFT.fft xs) := by
  have ha := transform_accuracy xs false h
  refine ⟨ha.1, ?_⟩
  intro k hk
  have row := ha.2 k hk
  exact ⟨row.1.1, row.2.1.1, row.1.2, row.2.1.2⟩

#print axioms magnitude_safe
#print axioms radix2_admissible
#print axioms transform_accuracy
#print axioms fft_accuracy

end Verified.Examples.FFTTheorem
