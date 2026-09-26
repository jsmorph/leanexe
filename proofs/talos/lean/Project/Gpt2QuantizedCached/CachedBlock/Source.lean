import Project.Gpt2QuantizedCached.CachedBlock.Tensors

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized Project.ProofKit

theorem cachedBlock_tensors (weights input cache : ByteArray) (layer position : Nat) :
    Quantized.cachedBlock weights input cache layer position =
      let values := tensors weights input cache layer position
      if values.accepted then
        { status := 0, hidden := values.hidden,
          cache := Gpt2CachedStep.CachedBlock.cacheUpdate values.qkv }
      else { status := 4, hidden := .empty, cache := .empty } := by
  simp only [Quantized.cachedBlock, tensors, Tensors.accepted]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all [Gpt2CachedStep.CachedBlock.cacheUpdate]

#print axioms cachedBlock_tensors
end Project.Gpt2QuantizedCached.CachedBlock
