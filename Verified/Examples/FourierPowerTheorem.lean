import Verified.Examples.FourierPowerSpec
import Verified.Examples.FourierTheorem

namespace Verified.Examples.FourierPowerTheorem
open CodeLib.IEEE64 LeanExe.ProofKit.F64Approx
open FourierPowerSpec FourierPowerEmbedding

theorem componentError_nonneg (samples : Array Float) : 0 ≤ componentError samples := by
  unfold componentError
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr (FourierSpec.growth_ge_one _)) (sampleNorm_nonneg _))
    (FourierSpec.underflow_nonneg _)

theorem magnitudeBound_eq (samples : Array Float) :
    magnitudeBound samples = sampleNorm samples + componentError samples := by
  unfold magnitudeBound componentError
  ring

theorem componentError_embed (samples : Array Float) (hn : samples.size ≤ 2 ^ 32) :
    FourierSpec.errorBound (embed samples) = componentError samples := by
  unfold FourierSpec.errorBound componentError
  rw [embed_nSamples samples hn, inputNorm_embed samples hn]

theorem magnitudeBound_embed (samples : Array Float) (hn : samples.size ≤ 2 ^ 32) :
    FourierSpec.magnitudeBound (embed samples) = magnitudeBound samples := by
  unfold FourierSpec.magnitudeBound magnitudeBound
  rw [embed_nSamples samples hn, inputNorm_embed samples hn]

theorem embed_admissible (samples : Array Float) (h : Admissible samples) :
    FourierSpec.Admissible (embed samples) := by
  refine ⟨by rw [embed_nSamples samples h.1]; exact h.1, ?_, ?_⟩
  · intro i hi
    apply embed_finite samples h.1 h.2.1 i
    rw [embed_size samples h.1]
    simpa only [embed_nSamples samples h.1] using hi
  · rw [magnitudeBound_embed samples h.1]
    apply FourierPowerArithmetic.magnitude_safe _ _ h.2.2
    rw [magnitudeBound_eq]
    exact add_nonneg (sampleNorm_nonneg _) (componentError_nonneg _)

theorem powerSpectrum_accuracy (samples : Array Float) (h : Admissible samples) :
    Accuracy samples := by
  have hforward := FourierTheorem.dft_accuracy (embed samples) (embed_admissible samples h)
  refine ⟨powerSpectrum_size samples h.1, ?_⟩
  intro k hk
  have hkN : k < samples.size := by
    unfold powerCount at hk
    split at hk <;> omega
  have hkEmbed : k < (embed samples).size / 2 := by
    rw [embed_nSamples samples h.1]
    exact hkN
  have hrow := hforward.2 k hkEmbed
  let a := (Fourier.dft (embed samples))[2 * k]!
  let b := (Fourier.dft (embed samples))[2 * k + 1]!
  have ha : FApprox a (realPart samples k) (componentError samples) := by
    refine ⟨hrow.1, ?_⟩
    have he := hrow.2.2.1
    rwa [realDFT_embed samples h.1 k, componentError_embed samples h.1] at he
  have hb : FApprox b (imagPart samples k) (componentError samples) := by
    refine ⟨hrow.2.1, ?_⟩
    have he := hrow.2.2.2
    rwa [imagDFT_embed samples h.1 k, componentError_embed samples h.1] at he
  have hreal : |realPart samples k| ≤ sampleNorm samples := by
    have hr := FourierSpec.realDFT_abs_le_inputNorm (embed samples) k
    rwa [realDFT_embed samples h.1 k, inputNorm_embed samples h.1] at hr
  have himag : |imagPart samples k| ≤ sampleNorm samples := by
    have hi := FourierSpec.imagDFT_abs_le_inputNorm (embed samples) k
    rwa [imagDFT_embed samples h.1 k, inputNorm_embed samples h.1] at hi
  have hsafe : FourierPowerArithmetic.squareMagnitude
      (sampleNorm samples + componentError samples) < (2 : ℝ) ^ 1022 := by
    rw [← magnitudeBound_eq]
    exact h.2.2
  have hnear := FourierPowerArithmetic.square_sum_near a b (realPart samples k)
    (imagPart samples k) (sampleNorm samples) (componentError samples) ha hb hreal himag hsafe
  have hnonneg := FourierPowerArithmetic.square_sum_nonneg a b (realPart samples k)
    (imagPart samples k) (sampleNorm samples) (componentError samples) ha hb hreal himag hsafe
  have herror : FourierPowerArithmetic.powerError (sampleNorm samples)
      (componentError samples) = errorBound samples := by
    unfold FourierPowerArithmetic.powerError errorBound
    rw [magnitudeBound_eq]
  rw [herror] at hnear
  rw [powerSpectrum_get samples h.1 k hk]
  exact ⟨hnear.1, hnonneg, hnear.2⟩

#print axioms embed_admissible
#print axioms powerSpectrum_accuracy

end Verified.Examples.FourierPowerTheorem
