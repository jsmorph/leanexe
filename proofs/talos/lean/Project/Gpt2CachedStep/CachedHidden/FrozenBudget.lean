import Project.Gpt2CachedStep.CachedHidden.FrozenPlan
import Project.Gpt2CachedStep.CachedBlock.FrozenBudget

namespace Project.Gpt2CachedStep.Frozen.CachedHidden
open Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem updatesNeed_le (layer : Nat) (hLayer : layer < 12) :
    (updatesNeed layer).toNat ≤ 73736 := by
  rw [updatesNeed, PackedCapacity.capacity_toNat _ (by omega)]
  exact (PackedCapacity.capacityNat_le _).trans (by omega)

theorem stepHeap_top (heap : Heap) (input updates : FreeNode) (position layer : Nat) :
    (stepHeap heap input updates position layer).top = (appendHeap heap position layer).top := by
  by_cases h : layer = 0 <;> simp [stepHeap, oldReleaseHeap, cacheReleasedHeap, h]

theorem layer_budget (heap : Heap) (input updates : FreeNode) (position layer : Nat)
    (hPosition : position < 128) (hLayer : layer < 12)
    (h : heap.top.toNat + 196608 < 4294967296) :
    LayerResources heap position layer 65536 ∧
      (stepHeap heap input updates position layer).top.toNat ≤ heap.top.toNat + 196608 := by
  obtain ⟨hBlock, hBlockTop⟩ := CachedBlock.budget heap position hPosition (by omega)
  have hNeed := updatesNeed_le layer hLayer
  have hAppend := (CachedBlock.finalHeap heap position).allocate_top_le (updatesNeed layer)
  rw [← appendHeap] at hAppend
  refine ⟨⟨hBlock, LayerNorm.AllocationFits.of_bound (by omega)⟩, ?_⟩
  rw [stepHeap_top]
  omega

theorem traversal_budget (heap : Heap) (embedding : FreeNode) (position : Nat)
    (hPosition : position < 128) (h : heap.top.toNat + 2359296 < 4294967296) :
    TraversalResources heap embedding position 65536 ∧
      (traversal heap embedding position 12).heap.top.toNat ≤ heap.top.toNat + 2359296 := by
  have hTop : ∀ layer, layer ≤ 12 →
      (traversal heap embedding position layer).heap.top.toNat ≤ heap.top.toNat + layer * 196608 := by
    intro layer
    induction layer with
    | zero => intro _; exact Nat.le_refl _
    | succ layer ih =>
      intro hLayer
      have hBefore := ih (by omega)
      have hStep := (layer_budget (traversal heap embedding position layer).heap
        (traversal heap embedding position layer).hidden (traversal heap embedding position layer).updates
        position layer hPosition (by omega) (by omega)).2
      change (stepHeap _ _ _ _ _).top.toNat ≤ _
      omega
  refine ⟨⟨?_⟩, hTop 12 (by omega)⟩
  intro layer hLayer
  have hBefore := hTop layer (by omega)
  exact (layer_budget (traversal heap embedding position layer).heap
    (traversal heap embedding position layer).hidden (traversal heap embedding position layer).updates
    position layer hPosition hLayer (by omega)).1

theorem cacheNeed_le (cacheSize : Nat) (hSize : cacheSize ≤ 127 * 73728) :
    (cacheNeed cacheSize).toNat ≤ 9437192 := by
  rw [cacheNeed, PackedCapacity.capacity_toNat _ (by omega)]
  exact (PackedCapacity.capacityNat_le _).trans (by omega)

theorem budget (heap : Heap) (position cacheSize : Nat)
    (hPosition : position < 128) (hSize : cacheSize = position * 73728)
    (h : heap.top.toNat + 12582912 < 4294967296) :
    Resources heap position cacheSize 65536 ∧
      (finalHeap heap position cacheSize).top.toNat ≤ heap.top.toNat + 12582912 := by
  have hEmbeddingNeed : embeddingNeed.toNat = 3072 := rfl
  have hEmbedding := heap.allocate_top_le embeddingNeed
  rw [← embeddingHeap, hEmbeddingNeed] at hEmbedding
  obtain ⟨hLayers, hLayersTop⟩ := traversal_budget (embeddingHeap heap) (embeddingNode heap)
    position hPosition (by omega)
  change (traversed heap position).heap.top.toNat ≤ (embeddingHeap heap).top.toNat + 2359296 at hLayersTop
  have hNeed := cacheNeed_le cacheSize (by omega)
  have hCache := (traversed heap position).heap.allocate_top_le (cacheNeed cacheSize)
  rw [← cacheHeap] at hCache
  refine ⟨⟨LayerNorm.AllocationFits.of_bound (by omega), hLayers,
    LayerNorm.AllocationFits.of_bound (by omega)⟩, ?_⟩
  simp only [finalHeap, Heap.release_top]
  omega

#print axioms budget

end Project.Gpt2CachedStep.Frozen.CachedHidden
