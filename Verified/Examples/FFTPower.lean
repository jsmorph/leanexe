import Verified.Examples.FFTTheorem
import Verified.Examples.FourierPowerTheorem

namespace Verified.Examples.FFTPower

open CodeLib.IEEE64 LeanExe.ProofKit.F64Approx FFTSpec FourierPowerEmbedding

theorem embed_admissible (samples : Array Float) (h : PowerAdmissible samples) :
    Admissible (embed samples) := by
  refine ⟨by rw [embed_nSamples samples h.1]; exact h.1, ?_, ?_⟩
  · intro i hi
    apply embed_finite samples h.1 h.2.1 i
    rw [embed_size samples h.1]
    simpa only [embed_nSamples samples h.1] using hi
  · rw [embed_nSamples samples h.1, inputNorm_embed samples h.1]
    have hs := h.2.2
    by_cases hr : FFT.isRadix2 (UInt64.ofNat samples.size) = true
    · rw [ite_eq_left hr] at hs ⊢
      exact hs.1
    · rw [ite_eq_right hr] at hs ⊢
      rw [FourierPowerTheorem.magnitudeBound_embed samples h.1]
      apply FourierPowerArithmetic.magnitude_safe _ _ hs
      rw [FourierPowerTheorem.magnitudeBound_eq]
      exact add_nonneg (sampleNorm_nonneg _) (FourierPowerTheorem.componentError_nonneg _)

theorem square_safe (samples : Array Float) (h : PowerAdmissible samples) :
    FourierPowerArithmetic.squareMagnitude (magnitudeBound (embed samples)) < (2 : ℝ) ^ 1022 := by
  unfold magnitudeBound
  rw [embed_nSamples samples h.1, inputNorm_embed samples h.1]
  have hs := h.2.2
  by_cases hr : FFT.isRadix2 (UInt64.ofNat samples.size) = true
  · rw [ite_eq_left hr] at hs ⊢
    exact hs.2
  · rw [ite_eq_right hr] at hs ⊢
    rwa [FourierPowerTheorem.magnitudeBound_embed samples h.1]

theorem powerSpectrum_accuracy (samples : Array Float) (h : PowerAdmissible samples) :
    AccuratePower samples (FFT.powerSpectrum samples) := by
  have ha := FFTTheorem.transform_accuracy (embed samples) false (embed_admissible samples h)
  refine ⟨FFTLoop.powerSpectrum_size samples h.1, ?_⟩
  intro k hk
  have hkN : k < samples.size := by
    unfold powerCount at hk
    split at hk <;> omega
  have hkEmbed : k < (embed samples).size / 2 := by
    rw [embed_nSamples samples h.1]
    exact hkN
  have row := ha.2 k hkEmbed
  let a := (FFT.fft (embed samples))[2 * k]!
  let b := (FFT.fft (embed samples))[2 * k + 1]!
  have hre : FApprox a (realPart samples k) (errorBound (embed samples)) := by
    have hr := row.1
    rwa [realDFT_embed samples h.1 k] at hr
  have him : FApprox b (imagPart samples k) (errorBound (embed samples)) := by
    have hi := row.2.1
    rwa [imagDFT_embed samples h.1 k] at hi
  have hreal : |realPart samples k| ≤ sampleNorm samples := by
    have hr := FourierSpec.realDFT_abs_le_inputNorm (embed samples) k
    rwa [realDFT_embed samples h.1 k, inputNorm_embed samples h.1] at hr
  have himag : |imagPart samples k| ≤ sampleNorm samples := by
    have hi := FourierSpec.imagDFT_abs_le_inputNorm (embed samples) k
    rwa [imagDFT_embed samples h.1 k, inputNorm_embed samples h.1] at hi
  have hsafe : FourierPowerArithmetic.squareMagnitude
      (sampleNorm samples + errorBound (embed samples)) < (2 : ℝ) ^ 1022 := by
    have hs := square_safe samples h
    rwa [FFTTheorem.magnitudeBound_eq, inputNorm_embed samples h.1] at hs
  have hnear := FourierPowerArithmetic.square_sum_near a b (realPart samples k)
    (imagPart samples k) (sampleNorm samples) (errorBound (embed samples)) hre him hreal himag hsafe
  have hnonneg := FourierPowerArithmetic.square_sum_nonneg a b (realPart samples k)
    (imagPart samples k) (sampleNorm samples) (errorBound (embed samples)) hre him hreal himag hsafe
  have heq : FourierPowerArithmetic.powerError (sampleNorm samples) (errorBound (embed samples)) =
      powerError samples := by
    unfold FourierPowerArithmetic.powerError powerError
    rw [FFTTheorem.magnitudeBound_eq, inputNorm_embed samples h.1]
  rw [heq] at hnear
  rw [FFTLoop.powerSpectrum_get samples h.1 k hk]
  exact ⟨hnear.1, hnonneg, hnear.2⟩

#print axioms embed_admissible
#print axioms square_safe
#print axioms powerSpectrum_accuracy

end Verified.Examples.FFTPower
