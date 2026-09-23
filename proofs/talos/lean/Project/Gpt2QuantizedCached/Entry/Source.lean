import Project.Gpt2QuantizedCached.CachedHidden.Spec
import Project.Gpt2QuantizedCached.Model

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

def invalidInput (cache : ByteArray) (token : UInt32) (position : Nat) : Bool :=
  token.toNat ≥ 50257 || position ≥ 128 || cache.size != position * cachePositionWords * 4

def normalizedHidden (weights : ByteArray) (hidden : HiddenResult) : ByteArray :=
  LeanExe.Models.Gpt2.layerNorm weights hidden.hidden (finalNormOffset / 4) (finalNormOffset / 4 + 768) 1

def vocabulary (weights normalized : ByteArray) : ByteArray :=
  linearGroupedRows weights normalized tokenWeightOffset tokenScaleOffset 0 768 50257 1 false

def finishStep (hidden : HiddenResult) (normalized logits : ByteArray) (position : Nat) : CachedResult :=
  if hidden.status != 0 then ⟨hidden.status, .empty, .empty⟩
  else if !finiteWords normalized 0 768 then ⟨4, .empty, .empty⟩
  else if !finiteWords hidden.cache 0 ((position + 1) * cachePositionWords) ||
      !finiteWords logits 0 50257 then ⟨4, .empty, .empty⟩
  else ⟨0, hidden.cache, logits⟩

theorem cachedStep_eq (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    cachedStep weights cache token position =
      if !validHeader weights then ⟨1, .empty, .empty⟩
      else if invalidInput cache token position then ⟨3, .empty, .empty⟩
      else if !finiteWords cache 0 (position * cachePositionWords) then ⟨3, .empty, .empty⟩
      else
        let hidden := cachedHidden weights cache token position
        let normalized := normalizedHidden weights hidden
        finishStep hidden normalized (vocabulary weights normalized) position := by
  rfl

theorem invalidInput_false (cache : ByteArray) (token : UInt32) (position : Nat) :
    invalidInput cache token position = false ↔
      token.toNat < 50257 ∧ position < 128 ∧ cache.size = position * 73728 := by
  simp only [invalidInput, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le,
    bne_eq_false_iff_eq, cachePositionWords]
  constructor
  · rintro ⟨⟨ht, hp⟩, hc⟩
    exact ⟨ht, hp, by simpa only [Nat.mul_assoc] using hc⟩
  · rintro ⟨ht, hp, hc⟩
    exact ⟨⟨ht, hp⟩, by simpa only [Nat.mul_assoc] using hc⟩

theorem valid_extents (weights cache : ByteArray) (token : UInt32) (position : Nat)
    (hHeader : validHeader weights = true) (hInput : invalidInput cache token position = false) :
    tokenScaleOffset + token.toNat * 4 + 4 ≤ weights.size ∧
    tokenWeightOffset + token.toNat * 768 + 768 ≤ weights.size ∧
    positionOffset + (position * 768 + 768) * 4 ≤ weights.size ∧
    blocksOffset + 12 * blockBytes ≤ weights.size ∧
    finalNormOffset / 4 + 768 + 768 ≤ weights.size / 4 ∧
    position * 12 * 1536 * 4 ≤ cache.size ∧ cache.size + 73728 ≤ 4294967296 := by
  have hSize := Model.size_of_header weights hHeader
  rcases (invalidInput_false cache token position).mp hInput with ⟨ht, hp, hc⟩
  rw [hSize, hc]
  change 38597408 + token.toNat * 4 + 4 ≤ 127695972 ∧
    32 + token.toNat * 768 + 768 ≤ 127695972 ∧
    38798436 + (position * 768 + 768) * 4 ≤ 127695972 ∧
    127689828 ≤ 127695972 ∧ 31923993 ≤ 31923993 ∧
    position * 12 * 1536 * 4 ≤ position * 73728 ∧ position * 73728 + 73728 ≤ 4294967296
  omega

#print axioms cachedStep_eq
#print axioms invalidInput_false
#print axioms valid_extents
end Project.Gpt2QuantizedCached.Entry
