import Project.Gpt2QuantizedCached.CachedBlock.Resources

namespace Project.Gpt2QuantizedCached.CachedBlock
open Project.ProofKit Project.EulerRiemann.Execution
open GroupedProjection

theorem budget (heap : Heap) (position : Nat) (hPosition : position < 128)
    (h : heap.top.toNat + 98304 < 4294967296) :
    Resources heap position 65536 ∧ (cacheHeap heap position).top.toNat ≤ heap.top.toNat + 98304 := by
  have hQkvNeed : Projection.allocationBudget 768 2304 1 = 10176 := rfl
  have hProjectionNeed : Projection.allocationBudget 768 768 1 = 4032 := rfl
  have hExpandedNeed : Projection.allocationBudget 768 3072 1 = 13248 := rfl
  have hProjected2Need : Projection.allocationBudget 3072 768 1 = 6480 := rfl
  have hResidualNeed : residualNeed.toNat = 3072 := rfl
  have hActivatedNeed : activatedNeed.toNat = 12288 := rfl
  have hCacheNeed : cacheNeed.toNat = 6144 := rfl
  obtain ⟨hNormalized, hNormalizedTop⟩ := Gpt2CachedStep.LayerNorm.budget heap (by omega)
  change (normalizedHeap heap).top.toNat ≤ heap.top.toNat + 4096 at hNormalizedTop
  have hQkv := Projection.budget (normalizedHeap heap) 768 2304 1 (by rw [hQkvNeed]; omega)
  have hQkvTop := Projection.outputHeap_top (normalizedHeap heap) 768 2304 1
  rw [← qkvHeap, hQkvNeed] at hQkvTop
  obtain ⟨hAttention, hAttentionTop⟩ := Gpt2CachedStep.CachedAttention.budget
    (qkvHeap heap) position hPosition (by omega)
  change (attentionHeap heap position).top.toNat ≤ (qkvHeap heap).top.toNat + 24576 at hAttentionTop
  have hProjection := Projection.budget (attentionHeap heap position) 768 768 1
    (by rw [hProjectionNeed]; omega)
  have hProjectionTop := Projection.outputHeap_top (attentionHeap heap position) 768 768 1
  rw [← projectionHeap, hProjectionNeed] at hProjectionTop
  have hResidualTop := (projectionHeap heap position).allocate_top_le residualNeed
  rw [← residualHeap, hResidualNeed] at hResidualTop
  obtain ⟨hNormalized2, hNormalized2Top⟩ := Gpt2CachedStep.LayerNorm.budget
    (residualHeap heap position) (by omega)
  change (normalized2Heap heap position).top.toNat ≤ (residualHeap heap position).top.toNat + 4096 at hNormalized2Top
  have hExpanded := Projection.budget (normalized2Heap heap position) 768 3072 1
    (by rw [hExpandedNeed]; omega)
  have hExpandedTop := Projection.outputHeap_top (normalized2Heap heap position) 768 3072 1
  rw [← expandedHeap, hExpandedNeed] at hExpandedTop
  have hActivatedTop := (expandedHeap heap position).allocate_top_le activatedNeed
  rw [← activatedHeap, hActivatedNeed] at hActivatedTop
  have hProjected2 := Projection.budget (activatedHeap heap position) 3072 768 1
    (by rw [hProjected2Need]; omega)
  have hProjected2Top := Projection.outputHeap_top (activatedHeap heap position) 3072 768 1
  rw [← projected2Heap, hProjected2Need] at hProjected2Top
  have hHiddenTop := (projected2Heap heap position).allocate_top_le residualNeed
  have hCacheTop := (hiddenHeap heap position).allocate_top_le cacheNeed
  rw [← hiddenHeap, hResidualNeed] at hHiddenTop
  rw [← cacheHeap, hCacheNeed] at hCacheTop
  refine ⟨⟨hNormalized, hQkv, hAttention, hProjection, ?_, hNormalized2, hExpanded,
    ?_, hProjected2, ?_, ?_⟩, by omega⟩
  all_goals apply Gpt2CachedStep.LayerNorm.AllocationFits.of_bound
  all_goals simp only [hResidualNeed, hActivatedNeed, hCacheNeed]; omega

#print axioms budget
end Project.Gpt2QuantizedCached.CachedBlock
