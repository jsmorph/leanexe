import Project.Gpt2QuantizedCached.CachedHidden.Plan
import Project.Gpt2QuantizedCached.CachedHidden.TraversalBudget

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open Project.Gpt2CachedStep.LayerNorm (AllocationFits)

def hiddenBudget (cacheSize : Nat) : Nat := 1736456 + cacheSize

theorem finishBudget (initialTop : Nat) (heap : Heap) (status : UInt64) (cache updates : ByteArray)
    (hTop : heap.top.toNat ≤ initialTop + 1662672) (hUpdates : updates.size ≤ 73728)
    (hBound : initialTop + hiddenBudget cache.size < 4294967296) :
    AllocationFits heap (PackedAppend.need cache updates) 65536 ∧
      (finishHeap heap status cache updates).top.toNat ≤ initialTop + hiddenBudget cache.size := by
  have hNeed : (PackedAppend.need cache updates).toNat ≤ cache.size + 73736 := by
    rw [PackedAppend.need, PackedCapacity.capacity_toNat _ (by unfold hiddenBudget at hBound; omega)]
    exact (PackedCapacity.capacityNat_le _).trans (by omega)
  have hAppendBound : heap.top.toNat + 48 + (PackedAppend.need cache updates).toNat < 4294967296 := by
    unfold hiddenBudget at hBound
    omega
  refine ⟨AllocationFits.of_bound hAppendBound, ?_⟩
  have hAppendTop := heap.allocate_top_le (PackedAppend.need cache updates)
  simp only [finishHeap]
  split
  · unfold hiddenBudget
    omega
  · unfold hiddenBudget
    omega

theorem budget (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position : Nat)
    (hPosition : position < 128) (hBound : heap.top.toNat + hiddenBudget cache.size < 4294967296) :
    Resources heap weights cache token position 65536 ∧
      (finalHeap heap weights cache token position).top.toNat ≤ heap.top.toNat + hiddenBudget cache.size := by
  have hEmbeddingTop : (embeddingHeap heap).top.toNat ≤ heap.top.toNat + 3120 := by
    simpa only [embeddingHeap, show Embedding.need.toNat = 3072 from rfl, Nat.add_assoc] using
      heap.allocate_top_le Embedding.need
  have hEmbeddingFit : AllocationFits heap Embedding.need 65536 :=
    AllocationFits.of_bound (by change heap.top.toNat + 48 + 3072 < 4294967296; unfold hiddenBudget at hBound; omega)
  have hTraversalBound : (embeddingHeap heap).top.toNat + 1659552 < 4294967296 := by
    unfold hiddenBudget at hBound
    omega
  have hLayers := traversalResources (embeddingHeap heap) (embeddingNode heap) weights cache token position
    hPosition hTraversalBound
  have hTraversalEnd : (embeddingHeap heap).top.toNat + 1659552 ≤ heap.top.toNat + 1662672 := by
    omega
  have hTraversalTop : (traversed heap weights cache token position).heap.top.toNat ≤ heap.top.toNat + 1662672 := by
    unfold traversed
    exact Nat.le_trans (traversal_top (embeddingHeap heap) (embeddingNode heap) weights cache token position 12
      hPosition (by decide) hTraversalBound) hTraversalEnd
  have hUpdates : (layerPrefix weights cache token position 12).2.1.size ≤ 73728 :=
    (layerPrefix_valid weights cache token position 12).updates_le
  have hFinal := finishBudget heap.top.toNat (traversed heap weights cache token position).heap
    (layerPrefix weights cache token position 12).2.2 cache (layerPrefix weights cache token position 12).2.1
    hTraversalTop hUpdates hBound
  refine ⟨⟨hEmbeddingFit, hLayers, fun _ => hFinal.1⟩, ?_⟩
  unfold finalHeap cleanedHeap
  rw [Heap.release_top, Heap.release_top]
  exact hFinal.2

#print axioms finishBudget
#print axioms budget
end Project.Gpt2QuantizedCached.CachedHidden
