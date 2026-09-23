import Project.Gpt2QuantizedCached.CachedHidden.TraversalState
import Project.Gpt2QuantizedCached.CachedHidden.FinishBranch
import Project.Gpt2QuantizedCached.CachedHidden.FinishTail

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open Project.Gpt2CachedStep.LayerNorm (AllocationFits)

theorem traversalFinish_spec (env : HostEnv Unit) (initial embeddingStore traversedStore : Store Unit)
    (before embeddingHeap : Heap) (embeddingNode : FreeNode) (embeddingBytes cache : ByteArray)
    (cachePtr : UInt64) (params : List Value) (source : LayerState) (machine : Traversal) (traversedFrame : Locals)
    (hParams : params.length = 8) (hCachePtr : params[4]? = some (.i64 cachePtr))
    (hCacheSize : params[5]? = some (.i64 (UInt64.ofNat cache.size)))
    (hBefore : before.Frame initial embeddingHeap embeddingStore)
    (hCapacityBefore : embeddingStore.memoryCap «module» 0 = initial.memoryCap «module» 0)
    (hEmbedding : embeddingHeap.OwnsPacked embeddingStore embeddingNode embeddingBytes)
    (hEmbeddingFresh : before.FreshNode embeddingNode)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hCacheProtected : before.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hValid : ValidState 12 source) (hAppendSize : cache.size + 73728 ≤ 4294967296)
    (hFit : source.2.2 = 0 → AllocationFits machine.heap (PackedAppend.need cache source.2.1)
      (initial.memoryCap «module» 0))
    (hTraversal : TraversalStateAt embeddingStore embeddingHeap embeddingNode params source machine 12
      traversedStore traversedFrame)
    (Q : Assertion Unit)
    (hNext : ∀ (final : Store Unit) (result : Locals),
      result.values = resultValues source.2.2 machine.hidden (finishCacheNode machine.heap cache source.2.1)
        (finishValue source.2.2 source.1 cache source.2.1).hidden.size
        (finishValue source.2.2 source.1 cache source.2.1).cache.size →
      Completion before initial
        (cleanedHeap (finishHeap machine.heap source.2.2 cache source.2.1) embeddingNode machine.updates)
        final source.2.2 machine.hidden (finishCacheNode machine.heap cache source.2.1)
        (finishValue source.2.2 source.1 cache source.2.1).hidden
        (finishValue source.2.2 source.1 cache source.2.1).cache → Q (.Fallthrough final result)) :
    wp «module» ((func58.drop 60).take 48 ++ func58.drop 108) Q traversedStore traversedFrame env := by
  have hCombinedFrame := hBefore.trans hTraversal.preserved
  have hCapacity := hTraversal.capacity.trans hCapacityBefore
  have hUpdates := hTraversal.updatesOwned (by decide)
  have hCurrentEmbedding := hTraversal.preserved.ownsPacked hTraversal.heapAt hEmbedding
  have hUpdatesEmbedding := (hTraversal.updatesFresh (by decide)).owns_disjoint
    hUpdates.buffer.rootBound hEmbedding
  have hUpdatesFresh := hBefore.freshNode (hTraversal.updatesFresh (by decide))
  have hUpdateSize : source.2.1.size ≤ 73728 :=
    hValid.updates_le
  have hFit' : source.2.2 = 0 → AllocationFits machine.heap (PackedAppend.need cache source.2.1)
      (traversedStore.memoryCap «module» 0) := by
    rw [hCapacity]
    exact hFit
  apply finishBranch_spec env initial traversedStore before machine.heap
    params
    embeddingNode machine.updates
    machine.hidden cachePtr
    embeddingBytes source.2.1
    source.1 cache source.2.2
    traversedFrame hParams hCachePtr hCacheSize hTraversal.heapAt hCombinedFrame hCapacity hTraversal.pages
    hCurrentEmbedding hUpdates hTraversal.hidden
    (hCombinedFrame.packed hCacheProtected hCache) (hCombinedFrame.protects _ _ hCacheProtected)
    hEmbeddingFresh hUpdatesFresh
    (fun hZero => hBefore.freshNode (hTraversal.hiddenFresh (by decide) hZero)) hUpdatesEmbedding
    (fun hZero => (hTraversal.hiddenFresh (by decide) hZero).owns_disjoint
      (hTraversal.hidden.owned hZero).buffer.rootBound hEmbedding)
    (fun hZero => hTraversal.separated (by decide) hZero)
    ((Nat.add_le_add_left hUpdateSize cache.size).trans hAppendSize) hFit' hTraversal.state
  intro branchStore branchFrame hBranch hMemory
  apply finishTail_spec env initial branchStore before _
    params embeddingNode
    machine.updates machine.hidden
    (finishCacheNode machine.heap cache source.2.1) embeddingBytes
    source.2.1 _ _ source.2.2
    branchFrame hParams hMemory hBranch
  exact hNext

#print axioms traversalFinish_spec
end Project.Gpt2QuantizedCached.CachedHidden
