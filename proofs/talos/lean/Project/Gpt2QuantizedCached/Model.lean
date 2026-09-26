import LeanExe.Models.Gpt2.Quantized.Format
import Project.ProofKit.QuantizedValidity

namespace Project.Gpt2QuantizedCached.Model
open LeanExe.Models.Gpt2.Quantized Project.ProofKit.QuantizedValidity

structure Block (weights : ByteArray) (base : Nat) : Prop where
  normalization : finiteWords weights base 1536 = true
  qkvCoefficients : validCoefficients weights (base + qkvWeightOffset) (768 * 2304) = true
  qkvScales : validScales weights (base + qkvScaleOffset) 2304 = true
  qkvBias : finiteWords weights (base + qkvBiasOffset) 2304 = true
  attentionCoefficients : validCoefficients weights (base + attnWeightOffset) (768 * 768) = true
  attentionScales : validScales weights (base + attnScaleOffset) 768 = true
  attentionBiasAndNormalization : finiteWords weights (base + attnBiasOffset) (768 * 3) = true
  expansionCoefficients : validCoefficients weights (base + fcWeightOffset) (768 * 3072) = true
  expansionScales : validScales weights (base + fcScaleOffset) 3072 = true
  expansionBias : finiteWords weights (base + fcBiasOffset) 3072 = true
  contractionCoefficients : validCoefficients weights (base + mlpWeightOffset) (3072 * 768) = true
  contractionScales : validScales weights (base + mlpScaleOffset) 768 = true
  contractionBias : finiteWords weights (base + mlpBiasOffset) 768 = true

theorem validBlock_iff (weights : ByteArray) (base : Nat) :
    validBlock weights base = true ↔ Block weights base := by
  constructor
  · intro h
    simp [validBlock] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    simp [validBlock, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

structure Validated (weights : ByteArray) : Prop where
  header : validHeader weights = true
  tokenCoefficients : validCoefficients weights tokenWeightOffset (50257 * 768) = true
  tokenScales : validScales weights tokenScaleOffset 50257 = true
  positions : finiteWords weights positionOffset (1024 * 768) = true
  finalNormalization : finiteWords weights finalNormOffset 1536 = true
  blocks : ∀ layer < 12, Block weights (blocksOffset + layer * blockBytes)

theorem size_of_header (weights : ByteArray) (hHeader : validHeader weights = true) :
    weights.size = modelBytes := by
  simp [validHeader] at hHeader
  tauto

theorem Validated.size {weights : ByteArray} (hModel : Validated weights) :
    weights.size = modelBytes := size_of_header weights hModel.header

theorem Validated.block_extent {weights : ByteArray} (hModel : Validated weights)
    (layer : Nat) (hLayer : layer < 12) :
    blocksOffset + layer * blockBytes + blockBytes ≤ weights.size := by
  rw [hModel.size]
  change 41944164 + layer * 7145472 + 7145472 ≤ 127695972
  omega

theorem Validated.token_coefficient {weights : ByteArray} (hModel : Validated weights)
    (token channel : Nat) (hToken : token < 50257) (hChannel : channel < 768) :
    weights[tokenWeightOffset + token * 768 + channel]! ≠ 128 := by
  have h := (validCoefficients_iff weights tokenWeightOffset (50257 * 768)).mp
    hModel.tokenCoefficients (token * 768 + channel) (by omega)
  simpa only [Nat.add_assoc] using h

theorem Validated.token_scale {weights : ByteArray} (hModel : Validated weights)
    (token : Nat) (hToken : token < 50257) :
    0x00800000 ≤ LeanExe.Packed.getUInt32LE! weights (tokenScaleOffset + token * 4) ∧
    LeanExe.Packed.getUInt32LE! weights (tokenScaleOffset + token * 4) < 0x7F800000 :=
  (validScales_iff weights tokenScaleOffset 50257).mp hModel.tokenScales token hToken

#print axioms validBlock_iff
#print axioms size_of_header
#print axioms Validated.block_extent
#print axioms Validated.token_coefficient
#print axioms Validated.token_scale
end Project.Gpt2QuantizedCached.Model
