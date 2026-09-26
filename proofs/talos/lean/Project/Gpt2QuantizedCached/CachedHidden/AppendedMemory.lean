import Project.Gpt2QuantizedCached.CachedHidden.PendingOutput

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

structure AppendedMemory (before : Heap) (initial : Store Unit) (heap : Heap) (store : Store Unit)
    (hiddenNode updateNode cacheNode : FreeNode) (oldUpdates : ByteArray) (output : HiddenResult) : Prop
    extends PendingOutput before initial heap store output.status hiddenNode updateNode output.hidden
      (oldUpdates ++ output.cache) where
  cache : heap.StatusPacked store output.status cacheNode output.cache
  cacheFresh : output.status = 0 → before.FreshNode cacheNode
  hiddenCacheSep : output.status = 0 → regionsDisjoint hiddenNode.region cacheNode.region
  updatesCacheSep : output.status = 0 → regionsDisjoint updateNode.region cacheNode.region

theorem appendedMemory (before : Heap) (initial blockStore appendStore : Store Unit)
    (weights input cache updates : ByteArray) (layer position : Nat)
    (hInput : input.size = 3072)
    (hBlock : CachedBlock.Completion before initial
      (CachedBlock.executionHeap before position (CachedBlock.tensors weights input cache layer position)) blockStore
      (CachedBlock.tensors weights input cache layer position).accepted
      (CachedBlock.hiddenNode before position) (CachedBlock.cacheNode before position)
      (CachedBlock.tensors weights input cache layer position).hidden
      (Project.Gpt2CachedStep.CachedBlock.cacheUpdate (CachedBlock.tensors weights input cache layer position).qkv))
    (hFit : takeFirstFitFrom 0 (PackedAppend.need updates (cachedBlock weights input cache layer position).cache)
      (CachedBlock.executionHeap before position (CachedBlock.tensors weights input cache layer position)).nodes = none →
      (CachedBlock.executionHeap before position (CachedBlock.tensors weights input cache layer position)).top.toNat +
        48 + (PackedAppend.need updates (cachedBlock weights input cache layer position).cache).toNat ≤ 4294967296)
    (hAppend : (CachedBlock.executionHeap before position (CachedBlock.tensors weights input cache layer position)).PackedOutput
      blockStore appendStore (PackedAppend.need updates (cachedBlock weights input cache layer position).cache)
      (updates ++ (cachedBlock weights input cache layer position).cache)) :
    AppendedMemory before initial
      (appendedHeap before position (CachedBlock.tensors weights input cache layer position) updates
        (cachedBlock weights input cache layer position)) appendStore
      (CachedBlock.hiddenNode before position)
      (updatesNode before position (CachedBlock.tensors weights input cache layer position) updates
        (cachedBlock weights input cache layer position))
      (CachedBlock.cacheNode before position) updates (cachedBlock weights input cache layer position) := by
  have hPacked := hBlock.sourcePacked weights input cache layer position hInput
  have hFresh := (CachedBlock.executionHeap before position (CachedBlock.tensors weights input cache layer position)).freshNode_allocated
    (PackedAppend.need updates (cachedBlock weights input cache layer position).cache) hFit
  have hAccepted := (CachedBlock.cachedBlock_status_zero_iff weights input cache layer position).mp
  constructor
  · exact ⟨hAppend.heapAt, hAppend.frame.statusPacked hAppend.heapAt hPacked.1,
      hAppend.owned, hBlock.frame.trans hAppend.frame,
      fun hZero => (hBlock.fresh (hAccepted hZero)).1, hBlock.frame.freshNode hFresh,
      fun hZero => regionsDisjoint_symm
        (hFresh.owns_disjoint hAppend.owned.buffer.rootBound (hPacked.1.owned hZero)),
      hAppend.pages, (hAppend.memoryCap «module» 0).trans hBlock.memoryCap⟩
  · exact hAppend.frame.statusPacked hAppend.heapAt hPacked.2
  · exact fun hZero => (hBlock.fresh (hAccepted hZero)).2
  · exact fun hZero => hBlock.separated (hAccepted hZero)
  · exact fun hZero => hFresh.owns_disjoint hAppend.owned.buffer.rootBound (hPacked.2.owned hZero)

#print axioms appendedMemory
end Project.Gpt2QuantizedCached.CachedHidden
