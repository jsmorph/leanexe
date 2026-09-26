import Project.Gpt2QuantizedCached.CachedBlock.Source

namespace Project.Gpt2QuantizedCached.CachedBlock
open LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized Project.ProofKit

theorem cachedBlock_sizes (weights input cache : ByteArray) (layer position : Nat)
    (hInput : input.size = 3072) :
    let result := Quantized.cachedBlock weights input cache layer position
    (result.status = 0 ∧ result.hidden.size = 3072 ∧ result.cache.size = 6144) ∨
      (result.status = 4 ∧ result.hidden = .empty ∧ result.cache = .empty) := by
  rw [cachedBlock_tensors]
  have hSizes := tensors_sizes weights input cache layer position hInput
  generalize hValues : tensors weights input cache layer position = values at hSizes ⊢
  cases hAccepted : values.accepted
  · simp only [hAccepted, Bool.false_eq_true, ite_false]
    exact Or.inr ⟨trivial, trivial, trivial⟩
  · simp only [hAccepted, ite_true]
    exact Or.inl ⟨trivial, hSizes.hidden, Gpt2CachedStep.CachedBlock.cacheUpdate_size _⟩

#print axioms cachedBlock_sizes
end Project.Gpt2QuantizedCached.CachedBlock
