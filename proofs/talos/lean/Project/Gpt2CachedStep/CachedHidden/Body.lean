import Project.Gpt2CachedStep.CachedHidden.Cleanup
import Project.Gpt2CachedStep.CachedHidden.Plan

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2

set_option maxRecDepth 32768 in
theorem emitted_body : func36 = func36.take 49 ++ (func36.drop 49).take 26 ++
    (func36.drop 75).take 1 ++ (func36.drop 76).take 44 ++ (func36.drop 120).take 47 ++ func36.drop 167 := rfl

theorem body_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hToken : token.toNat < 50257) (hPosition : position < 128)
    (hTokenSize : 4 * (token.toNat * 768 + 768) ≤ weights.size)
    (hPositionSize : 4 * (positionOffset + position * 768 + 768) ≤ weights.size)
    (hWeightsSize : (blocksOffset + 12 * blockWords) * 4 ≤ weights.size)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hAppendSize : cache.size + 73728 ≤ 4294967296)
    (hResources : Resources heap position cache.size (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
    (hLocals : frame.locals.length = 119) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit)
    (hNext : ∀ final result,
      result.values = [.i64 (UInt64.ofNat (cache.size + 73728)),
        .i64 (cacheNode heap position cache.size).root, .i64 (cacheNode heap position cache.size).root,
        .i64 3072, .i64 (traversed heap position).hidden.root, .i64 (traversed heap position).hidden.root] →
      (finalHeap heap position cache.size).At final →
      (finalHeap heap position cache.size).OwnsPacked final (traversed heap position).hidden
        (layerPrefix weights cache token position 12).1 →
      (finalHeap heap position cache.size).OwnsPacked final (cacheNode heap position cache.size)
        (cache ++ (layerPrefix weights cache token position 12).2) →
      heap.Frame initial (finalHeap heap position cache.size) final →
      heap.FreshNode (traversed heap position).hidden → heap.FreshNode (cacheNode heap position cache.size) →
      regionsDisjoint (traversed heap position).hidden.region (cacheNode heap position cache.size).region →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      Q (.Fallthrough final result)) : wp «module» func36 Q initial frame env := by
  have hUpdatesSize : (layerPrefix weights cache token position 12).2.size = 73728 :=
    (layerPrefix_sizes weights cache token position 12).2
  have hNeed : PackedAppend.need cache (layerPrefix weights cache token position 12).2 = cacheNeed cache.size := by
    simp only [PackedAppend.need, cacheNeed, hUpdatesSize]
  have hEmbeddingFresh := heap.freshNode_allocated embeddingNeed (fun h => (hResources.embedding h).1.le)
  rw [emitted_body]
  simp only [List.append_assoc]
  apply embedding_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr weights cache token position frame
    hHeap hWeights hTokenSize hPositionSize hToken hPosition hWeightsProtected hResources.embedding hPages
    hParams hLocals hValues hTyped
  intro embeddingStore embeddingFrame hEmbeddingState hEmbeddingOutput
  apply initializeLayer_spec env embeddingStore _ (embeddingNode heap).root embeddingFrame rfl hEmbeddingState
  intro loopFrame hLoopState
  have hLayers : TraversalResources (embeddingHeap heap) (embeddingNode heap) position
      (embeddingStore.memoryCap «module» 0) := by rw [hEmbeddingOutput.memoryCap]; exact hResources.layers
  apply layerLoop_spec env embeddingStore (embeddingHeap heap) (embeddingNode heap)
    weightsOwner weightsPtr cacheOwner cachePtr weights cache token position loopFrame
    hEmbeddingOutput.heapAt hEmbeddingOutput.owned
    (hEmbeddingOutput.frame.packed hWeightsProtected hWeights) (hEmbeddingOutput.frame.packed hCacheProtected hCache)
    (hEmbeddingOutput.frame.protects _ _ hWeightsProtected) (hEmbeddingOutput.frame.protects _ _ hCacheProtected)
    hPosition hCacheSize hWeightsSize hLayers hEmbeddingOutput.pages hLoopState
  intro traversedStore traversedFrame hTraversal
  have hCombinedFrame := hEmbeddingOutput.frame.trans hTraversal.preserved
  have hUpdates := hTraversal.updatesOwned (by decide)
  have hHidden := hTraversal.hidden
  have hEmbedding := hTraversal.preserved.ownsPacked hTraversal.heapAt hEmbeddingOutput.owned
  have hUpdatesEmbedding := (hTraversal.updatesFresh (by decide)).owns_disjoint hUpdates.buffer.rootBound hEmbeddingOutput.owned
  have hHiddenEmbedding := (hTraversal.hiddenFresh (by decide)).owns_disjoint hHidden.buffer.rootBound hEmbeddingOutput.owned
  have hHiddenFresh := hEmbeddingOutput.frame.freshNode (hTraversal.hiddenFresh (by decide))
  have hUpdatesFresh := hEmbeddingOutput.frame.freshNode (hTraversal.updatesFresh (by decide))
  have hCacheResources : LayerNorm.AllocationFits (traversed heap position).heap (cacheNeed cache.size)
      (traversedStore.memoryCap «module» 0) := by
    rw [hTraversal.capacity, hEmbeddingOutput.memoryCap]
    exact hResources.cache
  have hCacheFresh := (traversed heap position).heap.freshNode_allocated (cacheNeed cache.size)
    (fun h => (hCacheResources h).1.le)
  apply cachePrepare_spec env traversedStore weightsOwner weightsPtr cacheOwner cachePtr
    (embeddingNode heap).root (traversed heap position).hidden.root (traversed heap position).updates.root
    weights cache token position (layerPrefix weights cache token position 12).2.size traversedFrame hTraversal.state
  intro preparedFrame hPrepared
  apply cacheAppend_spec env traversedStore (traversed heap position).heap _ (embeddingNode heap).root
    (traversed heap position).hidden.root (traversed heap position).updates.root cachePtr cache
    (layerPrefix weights cache token position 12).2 preparedFrame hTraversal.heapAt
    (hCombinedFrame.packed hCacheProtected hCache) hTraversal.updates
    (hCombinedFrame.protects _ _ hCacheProtected) hTraversal.updatesProtected
    (by rwa [hUpdatesSize]) (by rw [hNeed]; exact hCacheResources) hTraversal.pages rfl hPrepared
  intro appendStore appendFrame hAppendState hAppendOutput
  rw [hNeed] at hAppendState hAppendOutput
  have hCacheHidden := hCacheFresh.owns_disjoint hAppendOutput.owned.buffer.rootBound hHidden
  have hCacheUpdates := hCacheFresh.owns_disjoint hAppendOutput.owned.buffer.rootBound hUpdates
  have hCacheEmbedding := hCacheFresh.owns_disjoint hAppendOutput.owned.buffer.rootBound hEmbedding
  have hAppendFrame := hCombinedFrame.trans hAppendOutput.frame
  have hFinalCapacity := (hAppendOutput.memoryCap «module» 0).trans
    (hTraversal.capacity.trans (hEmbeddingOutput.memoryCap «module» 0))
  have hAppendState' : HiddenResultState
      (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      (embeddingNode heap).root (traversed heap position).updates.root
      (traversed heap position).hidden.root (cacheNode heap position cache.size).root
      (cache ++ (layerPrefix weights cache token position 12).2).size appendFrame := by
    simpa only [cacheNode, allocatedNode, ByteArray.size_append] using hAppendState
  have hCleanup := cleanup_spec env appendStore initial (cacheHeap heap position cache.size) heap _
    (embeddingNode heap) (traversed heap position).updates (traversed heap position).hidden (cacheNode heap position cache.size)
    (embedding weights token position) (layerPrefix weights cache token position 12).2
    (layerPrefix weights cache token position 12).1 (cache ++ (layerPrefix weights cache token position 12).2)
    appendFrame hAppendOutput.heapAt
    (hAppendOutput.frame.ownsPacked hAppendOutput.heapAt hEmbedding)
    (hAppendOutput.frame.ownsPacked hAppendOutput.heapAt hUpdates)
    (hAppendOutput.frame.ownsPacked hAppendOutput.heapAt hHidden) hAppendOutput.owned
    hUpdatesEmbedding (regionsDisjoint_symm hHiddenEmbedding) (regionsDisjoint_symm (hTraversal.separated (by decide)))
    (regionsDisjoint_symm hCacheEmbedding) (regionsDisjoint_symm hCacheUpdates)
    hAppendFrame hEmbeddingFresh hUpdatesFresh rfl hAppendState' Q []
  simp only [List.append_nil] at hCleanup
  apply hCleanup
  intro result hFinalHeap hFinalHidden hFinalCache hFinalFrame hReturned
  simp only [wp_nil]
  apply hNext _ result
  · simpa only [ByteArray.size_append, hUpdatesSize] using hReturned
  · exact hFinalHeap
  · exact hFinalHidden
  · exact hFinalCache
  · exact hFinalFrame
  · exact hHiddenFresh
  · exact hCombinedFrame.freshNode hCacheFresh
  · exact regionsDisjoint_symm hCacheHidden
  · exact hAppendOutput.pages
  · exact hFinalCapacity

#print axioms body_spec

end Project.Gpt2CachedStep.CachedHidden
