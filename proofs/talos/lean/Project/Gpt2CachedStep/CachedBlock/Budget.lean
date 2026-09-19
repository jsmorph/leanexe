import Project.Gpt2CachedStep.CachedBlock.Resources
import Project.Gpt2CachedStep.CachedAttention.Budget

namespace Project.Gpt2CachedStep.CachedBlock
open Project.ProofKit Project.EulerRiemann.Execution

theorem budget (heap : Heap) (position : Nat) (hPosition : position < 128)
    (h : heap.top.toNat + 98304 < 4294967296) :
    Resources heap position 65536 ∧ (finalHeap heap position).top.toNat ≤ heap.top.toNat + 98304 := by
  have hQkvNeed : qkvNeed.toNat = 9216 := rfl
  have hProjectionNeed : projectionNeed.toNat = 3072 := rfl
  have hExpandedNeed : expandedNeed.toNat = 12288 := rfl
  have hProjected2Need : projected2Need.toNat = 3072 := rfl
  have hCacheNeed : cacheNeed.toNat = 6144 := rfl
  obtain ⟨hNormalized, hNormalizedTop⟩ := LayerNorm.budget heap (by omega)
  change (normalizedHeap heap).top.toNat ≤ heap.top.toNat + 4096 at hNormalizedTop
  have hQkvTop := (normalizedHeap heap).allocate_top_le qkvNeed
  rw [← qkvHeap, hQkvNeed] at hQkvTop
  obtain ⟨hAttention, hAttentionTop⟩ := CachedAttention.budget (qkvHeap heap) position hPosition (by omega)
  change (attentionHeap heap position).top.toNat ≤ (qkvHeap heap).top.toNat + 24576 at hAttentionTop
  have hProjectionTop := (attentionHeap heap position).allocate_top_le projectionNeed
  have hResidualTop := (projectionHeap heap position).allocate_top_le projectionNeed
  rw [← projectionHeap, hProjectionNeed] at hProjectionTop
  rw [← residualHeap, hProjectionNeed] at hResidualTop
  obtain ⟨hNormalized2, hNormalized2Top⟩ := LayerNorm.budget (residualHeap heap position) (by omega)
  change (normalized2Heap heap position).top.toNat ≤ (residualHeap heap position).top.toNat + 4096 at hNormalized2Top
  have hExpandedTop := (normalized2Heap heap position).allocate_top_le expandedNeed
  have hActivatedTop := (expandedHeap heap position).allocate_top_le expandedNeed
  have hProjected2Top := (activatedHeap heap position).allocate_top_le projected2Need
  have hHiddenTop := (projected2Heap heap position).allocate_top_le projectionNeed
  have hCacheTop := (hiddenHeap heap position).allocate_top_le cacheNeed
  rw [← expandedHeap, hExpandedNeed] at hExpandedTop
  rw [← activatedHeap, hExpandedNeed] at hActivatedTop
  rw [← projected2Heap, hProjected2Need] at hProjected2Top
  rw [← hiddenHeap, hProjectionNeed] at hHiddenTop
  rw [← cacheHeap, hCacheNeed] at hCacheTop
  refine ⟨⟨hNormalized, ?_, hAttention, ?_, ?_, hNormalized2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals first
    | (apply LayerNorm.AllocationFits.of_bound
       omega)
    | (simp only [finalHeap, Heap.release_top]; omega)

#print axioms budget

end Project.Gpt2CachedStep.CachedBlock
