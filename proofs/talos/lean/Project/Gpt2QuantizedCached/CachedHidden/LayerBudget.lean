import Project.Gpt2QuantizedCached.CachedHidden.LayerPlan

namespace Project.Gpt2QuantizedCached.CachedHidden
open Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open Project.Gpt2CachedStep.LayerNorm (AllocationFits)

def layerBudget (layer : Nat) : Nat := 98360 + (layer + 1) * 6144

theorem updatesNeed_bound (updates cache : ByteArray) (layer : Nat)
    (hLayer : layer < 12) (hUpdates : updates.size ≤ layer * 6144) (hCache : cache.size ≤ 6144) :
    (PackedAppend.need updates cache).toNat ≤ (layer + 1) * 6144 + 8 := by
  rw [PackedAppend.need, PackedCapacity.capacity_toNat _ (by omega)]
  exact (PackedCapacity.capacityNat_le _).trans (by omega)

theorem layerBudget_spec (heap : Heap) (position layer : Nat) (values : CachedBlock.Tensors)
    (updates : ByteArray) (output : HiddenResult) (inputNode oldUpdates : FreeNode)
    (hPosition : position < 128) (hLayer : layer < 12)
    (hUpdates : updates.size ≤ layer * 6144) (hCache : output.cache.size ≤ 6144)
    (hBound : heap.top.toNat + layerBudget layer < 4294967296) :
    LayerResources heap position values updates output 65536 ∧
      (activeHeap heap inputNode oldUpdates position layer values updates output).top.toNat ≤
        heap.top.toNat + layerBudget layer := by
  have hBlockBound : heap.top.toNat + 98304 < 4294967296 := by
    unfold layerBudget at hBound
    omega
  have hBlock := (CachedBlock.budget heap position hPosition hBlockBound).1
  have hTop := CachedBlock.executionHeap_top heap position values hPosition hBlockBound
  have hNeed := updatesNeed_bound updates output.cache layer hLayer hUpdates hCache
  have hAppend := (CachedBlock.executionHeap heap position values).allocate_top_le
    (PackedAppend.need updates output.cache)
  constructor
  · refine ⟨hBlock, AllocationFits.of_bound ?_⟩
    unfold layerBudget at hBound
    omega
  · simp only [activeHeap, oldReleasedHeap_top, cacheReleasedHeap_top, appendedHeap]
    unfold layerBudget
    omega

#print axioms updatesNeed_bound
#print axioms layerBudget_spec
end Project.Gpt2QuantizedCached.CachedHidden
