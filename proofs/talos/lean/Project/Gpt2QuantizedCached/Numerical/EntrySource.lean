import Project.Gpt2QuantizedCached.Numerical.EntryGuard

namespace Project.Gpt2QuantizedCached.Numerical.EntrySource
open LeanExe.Models.Gpt2

theorem cachedStep_gated (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    Quantized.cachedStep weights cache token position =
      gated (!Quantized.validHeader weights) (Entry.invalidInput cache token position)
        (!Quantized.finiteWords cache 0 (position * cachePositionWords))
        (Quantized.cachedHidden weights cache token position)
        (Entry.normalizedHidden weights (Quantized.cachedHidden weights cache token position))
        (Entry.vocabulary weights (Entry.normalizedHidden weights (Quantized.cachedHidden weights cache token position))) position := rfl

theorem quantized_success (weights cache : ByteArray) (token : UInt32) (position : Nat)
    (h : (Quantized.cachedStep weights cache token position).status = 0) :
    (Quantized.cachedStep weights cache token position).cache = (Quantized.cachedHidden weights cache token position).cache ∧
      (Quantized.cachedStep weights cache token position).logits =
        Entry.vocabulary weights (Entry.normalizedHidden weights (Quantized.cachedHidden weights cache token position)) := by
  have hg := gated_success (!Quantized.validHeader weights) (Entry.invalidInput cache token position)
    (!Quantized.finiteWords cache 0 (position * cachePositionWords))
    (Quantized.cachedHidden weights cache token position)
    (Entry.normalizedHidden weights (Quantized.cachedHidden weights cache token position))
    (Entry.vocabulary weights (Entry.normalizedHidden weights (Quantized.cachedHidden weights cache token position))) position
    (by rwa [← cachedStep_gated])
  simpa only [← cachedStep_gated] using hg

theorem reference_success (weights cache : ByteArray) (token : UInt32) (position : Nat)
    (hw : weights.size = parameterWords * 4) (ht : token.toNat < vocabulary) (hp : position < 128)
    (hc : cache.size = position * cachePositionWords * 4) :
    (cachedStep weights cache token position).cache = (cachedHidden weights cache token position).cache ∧
      (cachedStep weights cache token position).logits = vocabularyHead weights
        (layerNorm weights (cachedHidden weights cache token position).hidden finalNormOffset (finalNormOffset + 768) 1) := by
  simp only [cachedStep, hw, hc, bne_self_eq_false, Bool.false_or, decide_eq_false (by omega : ¬token.toNat ≥ vocabulary),
    decide_eq_false (by omega : ¬position ≥ 128), Bool.false_eq_true, ite_false, and_self]

#print axioms quantized_success
#print axioms reference_success
end Project.Gpt2QuantizedCached.Numerical.EntrySource
