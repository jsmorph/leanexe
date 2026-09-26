import Project.Gpt2QuantizedCached.CachedHidden.FinishPlan

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem finishMemory_append (before heap : Heap) (original initial final : Store Unit)
    (embedding updates hidden : FreeNode) (embeddingBytes updatesBytes hiddenBytes cache : ByteArray)
    (hEmbedding : heap.OwnsPacked initial embedding embeddingBytes)
    (hUpdates : heap.OwnsPacked initial updates updatesBytes)
    (hHidden : heap.OwnsPacked initial hidden hiddenBytes)
    (hFrame : before.Frame original heap initial)
    (hCapacity : initial.memoryCap «module» 0 = original.memoryCap «module» 0)
    (hEmbeddingFresh : before.FreshNode embedding) (hUpdatesFresh : before.FreshNode updates)
    (hHiddenFresh : before.FreshNode hidden)
    (hTemporarySep : regionsDisjoint updates.region embedding.region)
    (hHiddenEmbedding : regionsDisjoint hidden.region embedding.region)
    (hHiddenUpdates : regionsDisjoint hidden.region updates.region)
    (hFit : takeFirstFitFrom 0 (PackedAppend.need cache updatesBytes) heap.nodes = none →
      heap.top.toNat + 48 + (PackedAppend.need cache updatesBytes).toNat ≤ 4294967296)
    (hAppend : heap.PackedOutput initial final (PackedAppend.need cache updatesBytes) (cache ++ updatesBytes)) :
    FinishMemory before original (heap.allocate (PackedAppend.need cache updatesBytes)) final 0
      embedding updates hidden (finishCacheNode heap cache updatesBytes)
      embeddingBytes updatesBytes hiddenBytes (cache ++ updatesBytes) := by
  have hFresh := heap.freshNode_allocated (PackedAppend.need cache updatesBytes) hFit
  have hCacheHidden := hFresh.owns_disjoint hAppend.owned.buffer.rootBound hHidden
  constructor
  · exact ⟨hAppend.heapAt,
      ⟨fun _ => hAppend.frame.ownsPacked hAppend.heapAt hHidden, fun h => False.elim (h rfl)⟩,
      ⟨fun _ => hAppend.owned, fun h => False.elim (h rfl)⟩,
      hFrame.trans hAppend.frame, fun _ => hHiddenFresh, fun _ => hFrame.freshNode hFresh,
      fun _ => regionsDisjoint_symm hCacheHidden,
      hAppend.pages, (hAppend.memoryCap «module» 0).trans hCapacity⟩
  · exact hAppend.frame.ownsPacked hAppend.heapAt hEmbedding
  · exact hAppend.frame.ownsPacked hAppend.heapAt hUpdates
  · exact hEmbeddingFresh
  · exact hUpdatesFresh
  · exact hTemporarySep
  · exact fun _ => hHiddenEmbedding
  · exact fun _ => hHiddenUpdates
  · exact fun _ => hFresh.owns_disjoint hAppend.owned.buffer.rootBound hEmbedding
  · exact fun _ => hFresh.owns_disjoint hAppend.owned.buffer.rootBound hUpdates

#print axioms finishMemory_append
end Project.Gpt2QuantizedCached.CachedHidden
