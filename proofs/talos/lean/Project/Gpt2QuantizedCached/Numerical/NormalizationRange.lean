import Project.Gpt2CachedStep.LayerNorm.RangeCertificate
import Project.Gpt2CachedStep.LayerNorm.LowerBounds
import Project.Gpt2QuantizedCached.Numerical.LayerNormPair

namespace Project.Gpt2QuantizedCached.Numerical.NormalizationRange
open Project.ProofKit LeanExe.Models.Gpt2

noncomputable def parameters (p : Gpt2CachedStep.LayerNorm.RangeCertificate.Parameters) : LayerNormPair.Parameters :=
  ⟨Gpt2CachedStep.LayerNorm.RangeCertificate.bounds p, 1 / 1000, 1 / 1000⟩

theorem denominator_source (input : ByteArray) :
    Gpt2CachedStep.LayerNorm.RangeCertificate.denominator input =
      Gpt2RowInvStd.DenominatorError.denominator (Gpt2RowInvStd.variancePrefix input 0 (rowMean input 0) 768) := by
  simp only [Gpt2CachedStep.LayerNorm.RangeCertificate.denominator,
    Gpt2CachedStep.LayerNorm.RangeCertificate.mean_source,
    Gpt2CachedStep.LayerNorm.RangeCertificate.varianceSum_source,
    Gpt2RowInvStd.DenominatorError.denominator, Gpt2RowInvStd.DenominatorError.shifted, Gpt2RowInvStd.DenominatorError.variance]

theorem sound (weights input : ByteArray) (scaleOffset biasOffset : Nat) (X : Nat → ℝ)
    (p : Gpt2CachedStep.LayerNorm.RangeCertificate.Parameters)
    (h : Gpt2CachedStep.LayerNorm.RangeCertificate.check weights input scaleOffset biasOffset p = true)
    (hd : F32RangeCertificate.lowerAbsolute (Gpt2CachedStep.LayerNorm.RangeCertificate.denominator input) 1 1000 = true) :
    LayerNormPair.Ranges weights input scaleOffset biasOffset X (parameters p) := by
  have hl := F32RangeCertificate.lowerAbsolute_sound _ 1 1000 hd
  rw [denominator_source] at hl
  exact ⟨Gpt2CachedStep.LayerNorm.RangeCertificate.sound weights input scaleOffset biasOffset p h,
    by norm_num [parameters], Gpt2CachedStep.LayerNorm.LowerBounds.root_sum input X,
    by norm_num [parameters], by simpa [parameters] using hl.2⟩

#print axioms sound
end Project.Gpt2QuantizedCached.Numerical.NormalizationRange
