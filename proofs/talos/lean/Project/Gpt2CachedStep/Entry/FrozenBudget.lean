import Project.Gpt2CachedStep.Entry.FrozenPlan
import Project.Gpt2CachedStep.CachedHidden.FrozenBudget

namespace Project.Gpt2CachedStep.Frozen.Entry
open Project.ProofKit Project.EulerRiemann.Execution

theorem budget (heap : Heap) (position cacheSize : Nat)
    (hPosition : position < 128) (hSize : cacheSize = position * 73728)
    (h : heap.top.toNat + 16777216 < 4294967296) :
    Resources heap position cacheSize 65536 ∧
      (finalHeap heap position cacheSize).top.toNat ≤ heap.top.toNat + 16777216 := by
  obtain ⟨hHidden, hHiddenTop⟩ := CachedHidden.budget heap position cacheSize hPosition hSize (by omega)
  change (hiddenHeap heap position cacheSize).top.toNat ≤ heap.top.toNat + 12582912 at hHiddenTop
  obtain ⟨hNormalized, hNormalizedTop⟩ := LayerNorm.budget (hiddenHeap heap position cacheSize) (by omega)
  change (normalizedHeap heap position cacheSize).top.toNat ≤
    (hiddenHeap heap position cacheSize).top.toNat + 4096 at hNormalizedTop
  have hLogits := (normalizedHeap heap position cacheSize).allocate_top_le Vocabulary.outputNeed
  have hNeed : Vocabulary.outputNeed.toNat = 201032 := rfl
  rw [← logitsHeap, hNeed] at hLogits
  refine ⟨⟨hHidden, hNormalized, LayerNorm.AllocationFits.of_bound (by omega)⟩, ?_⟩
  simp only [finalHeap, Heap.release_top]
  omega

#print axioms budget

end Project.Gpt2CachedStep.Frozen.Entry
