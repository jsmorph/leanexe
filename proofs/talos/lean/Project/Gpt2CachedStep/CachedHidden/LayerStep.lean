import Project.Gpt2CachedStep.CachedHidden.Resources
import Project.Gpt2CachedStep.CachedHidden.LayerCacheRelease
import Project.Gpt2CachedStep.CachedHidden.LayerControl

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

set_option maxRecDepth 32768 in
theorem emitted_layerStep : (layerBody.drop 4).take 201 =
    (layerBody.drop 4).take 84 ++ (layerBody.drop 88).take 61 ++
    (layerBody.drop 149).take 8 ++ (layerBody.drop 157).take 14 ++
    (layerBody.drop 171).take 4 ++ (layerBody.drop 175).take 30 := rfl

theorem layerStep_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr embeddingPtr : UInt64) (inputNode oldUpdates : FreeNode)
    (weights input cache updates : ByteArray) (token : UInt32) (position layer : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hBefore : before.Frame original heap initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hInput : heap.OwnsPacked initial inputNode input)
    (hUpdates : ByteArrayAt initial.mem oldUpdates.root.toNat updates)
    (hUpdatesOwned : layer ≠ 0 → heap.OwnsPacked initial oldUpdates updates)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hUpdatesProtected : heap.Protects oldUpdates.root.toNat (oldUpdates.root.toNat + updates.size))
    (hInputFresh : layer ≠ 0 → before.FreshNode inputNode)
    (hUpdatesFresh : layer ≠ 0 → before.FreshNode oldUpdates)
    (hOldSeparated : layer ≠ 0 → regionsDisjoint inputNode.region oldUpdates.region)
    (hLayer : layer < 12) (hPosition : position < 128)
    (hInputSize : input.size = 3072) (hUpdatesSize : updates.size = layer * 6144)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hWeightsSize : (blocksOffset + layer * blockWords + blockWords) * 4 ≤ weights.size)
    (hResources : LayerResources heap position layer (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : LayerState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      embeddingPtr inputNode.root oldUpdates.root layer updates.size frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      LayerState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        embeddingPtr (CachedBlock.hiddenNode heap position).root (updatesNode heap position layer).root
        (layer + 1) (updates.size + 6144) result →
      (stepHeap heap inputNode oldUpdates position layer).At final →
      (stepHeap heap inputNode oldUpdates position layer).OwnsPacked final (CachedBlock.hiddenNode heap position)
        (cachedBlock weights input cache layer position).hidden →
      (stepHeap heap inputNode oldUpdates position layer).OwnsPacked final (updatesNode heap position layer)
        (updates ++ (cachedBlock weights input cache layer position).cache) →
      before.Frame original (stepHeap heap inputNode oldUpdates position layer) final →
      before.FreshNode (CachedBlock.hiddenNode heap position) → before.FreshNode (updatesNode heap position layer) →
      regionsDisjoint (CachedBlock.hiddenNode heap position).region (updatesNode heap position layer).region →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((layerBody.drop 4).take 201 ++ rest) Q initial frame env := by
  have hCacheBytes := CachedBlock.Spec.cachedBlock_cache_size weights input cache layer position
  have hNeed : PackedAppend.need updates (cachedBlock weights input cache layer position).cache = updatesNeed layer := by
    simp only [PackedAppend.need, updatesNeed, hCacheBytes, hUpdatesSize]
  rw [emitted_layerStep]
  simp only [List.append_assoc]
  apply layerCall_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr embeddingPtr inputNode.root oldUpdates.root
    weights input cache token position layer updates.size frame hHeap hWeights hInput.buffer.values hCache
    hWeightsProtected hInput.payload_protects hCacheProtected hLayer hPosition hInputSize hCacheSize hWeightsSize
    hResources.block hPages hState
  intro blockStore blockFrame hCallState hBlockHeap hHidden hBlockCache hBlockFrame hHiddenFresh hBlockCacheFresh hHiddenCache hBlockPages hBlockCap
  have hInputBlock := hBlockFrame.ownsPacked hBlockHeap hInput
  have hUpdatesBlock := hBlockFrame.packed hUpdatesProtected hUpdates
  have hUpdatesOwnedBlock (h : layer ≠ 0) := hBlockFrame.ownsPacked hBlockHeap (hUpdatesOwned h)
  have hBeforeBlock := hBefore.trans hBlockFrame
  have hHiddenInput := hHiddenFresh.owns_disjoint hHidden.buffer.rootBound hInput
  have hCacheInput := hBlockCacheFresh.owns_disjoint hBlockCache.buffer.rootBound hInput
  have hHiddenOldUpdates (h : layer ≠ 0) := hHiddenFresh.owns_disjoint hHidden.buffer.rootBound (hUpdatesOwned h)
  have hCacheOldUpdates (h : layer ≠ 0) := hBlockCacheFresh.owns_disjoint hBlockCache.buffer.rootBound (hUpdatesOwned h)
  have hAppendResources : LayerNorm.AllocationFits (CachedBlock.finalHeap heap position) (updatesNeed layer)
      (blockStore.memoryCap «module» 0) := by rw [hBlockCap]; exact hResources.append
  have hNewFresh := (CachedBlock.finalHeap heap position).freshNode_allocated (updatesNeed layer)
    (fun h => (hAppendResources h).1.le)
  apply layerAppend_spec env blockStore (CachedBlock.finalHeap heap position) _ embeddingPtr inputNode.root oldUpdates.root
    (CachedBlock.hiddenNode heap position).root (CachedBlock.cacheNode heap position).root updates
    (cachedBlock weights input cache layer position).cache layer blockFrame hBlockHeap hUpdatesBlock hBlockCache.buffer.values
    (hBlockFrame.protects _ _ hUpdatesProtected) hBlockCache.payload_protects
    (by rw [hCacheBytes, hUpdatesSize]; omega) hCacheBytes
    (by rw [hNeed]; exact hAppendResources) hBlockPages rfl hCallState
  intro appendStore appendFrame hAppendState hAppendOutput
  rw [hNeed] at hAppendOutput hAppendState
  have hAppHeap := hAppendOutput.heapAt
  have hAppFrame := hAppendOutput.frame
  have hAppHidden := hAppFrame.ownsPacked hAppHeap hHidden
  have hAppCache := hAppFrame.ownsPacked hAppHeap hBlockCache
  have hAppInput := hAppFrame.ownsPacked hAppHeap hInputBlock
  have hAppOldUpdates (h : layer ≠ 0) := hAppFrame.ownsPacked hAppHeap (hUpdatesOwnedBlock h)
  have hNewHidden := hNewFresh.owns_disjoint hAppendOutput.owned.buffer.rootBound hHidden
  have hNewCache := hNewFresh.owns_disjoint hAppendOutput.owned.buffer.rootBound hBlockCache
  have hNewInput := hNewFresh.owns_disjoint hAppendOutput.owned.buffer.rootBound hInputBlock
  have hNewOldUpdates (h : layer ≠ 0) := hNewFresh.owns_disjoint hAppendOutput.owned.buffer.rootBound (hUpdatesOwnedBlock h)
  have hCacheRoot := hAppCache.buffer.rootBound
  have hCacheRoot32 : (CachedBlock.cacheNode heap position).root.toNat ≤ 4294967296 := by
    have := hAppCache.buffer.addressBound
    omega
  have hAfterCacheHidden := hAppHidden.released (CachedBlock.cacheNode heap position) hCacheRoot hCacheRoot32 hHiddenCache
  have hAfterCacheNew := hAppendOutput.owned.released (CachedBlock.cacheNode heap position) hCacheRoot hCacheRoot32 hNewCache
  have hAfterCacheInput := hAppInput.released (CachedBlock.cacheNode heap position) hCacheRoot hCacheRoot32
    (regionsDisjoint_symm hCacheInput)
  have hAfterCacheOldUpdates (h : layer ≠ 0) := (hAppOldUpdates h).released (CachedBlock.cacheNode heap position)
    hCacheRoot hCacheRoot32 (regionsDisjoint_symm (hCacheOldUpdates h))
  have hAfterCacheFrame := (hBeforeBlock.trans hAppFrame).released (CachedBlock.cacheNode heap position)
    hCacheRoot hCacheRoot32 (hBefore.freshNode hBlockCacheFresh)
  apply layerCacheRelease_spec env appendStore (appendHeap heap position layer) _ embeddingPtr inputNode.root oldUpdates.root
    (CachedBlock.hiddenNode heap position).root (updatesNode heap position layer).root
    (CachedBlock.cacheNode heap position) (cachedBlock weights input cache layer position).cache layer updates.size
    appendFrame hAppHeap hAppCache
    (hAppCache.root_ne (regionsDisjoint_symm hHiddenCache)) (hAppCache.root_ne (regionsDisjoint_symm hNewCache)) rfl hAppendState
  intro releasedFrame hReleasedState hReleasedHeap
  apply prepareLayer_spec env _ _ embeddingPtr inputNode.root oldUpdates.root (CachedBlock.hiddenNode heap position).root
    (CachedBlock.cacheNode heap position).root (updatesNode heap position layer).root layer updates.size releasedFrame rfl hReleasedState
  intro preparedFrame hPrepared
  have hParamLength : preparedFrame.params.length = 8 := by rw [hPrepared.1.1]; rfl
  have hLocalLength := hPrepared.1.2.1
  have hPreparedOld := hPrepared.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hPreparedInput := hPrepared.1.2.2.2.2.2.2.2.1
  have hPreparedUpdates := hPrepared.1.2.2.2.2.2.2.2.2.2.2.1
  apply oldRelease_spec env _ (cacheReleasedHeap heap position layer) inputNode oldUpdates input updates layer preparedFrame
    hReleasedHeap (fun _ => hAfterCacheInput) hAfterCacheOldUpdates hOldSeparated hPrepared.1.2.2.1
  · simpa [Locals.get, hParamLength, hLocalLength] using hPreparedOld
  · simpa [Locals.get, hParamLength, hLocalLength] using hPreparedInput
  · simpa [Locals.get, hParamLength, hLocalLength] using hPreparedUpdates
  intro hFinalHeap
  let finalStore := oldReleaseStore (cacheReleasedHeap heap position layer)
    ((appendHeap heap position layer).releaseStore appendStore (CachedBlock.cacheNode heap position)) inputNode oldUpdates layer
  have hFinal :
      (stepHeap heap inputNode oldUpdates position layer).OwnsPacked finalStore (CachedBlock.hiddenNode heap position)
        (cachedBlock weights input cache layer position).hidden ∧
      (stepHeap heap inputNode oldUpdates position layer).OwnsPacked finalStore (updatesNode heap position layer)
        (updates ++ (cachedBlock weights input cache layer position).cache) ∧
      before.Frame original (stepHeap heap inputNode oldUpdates position layer) finalStore := by
    by_cases hZero : layer = 0
    · simpa only [finalStore, stepHeap, cacheReleasedHeap, appendHeap, updatesNode, oldReleaseHeap, oldReleaseStore, hZero, ite_true] using
        And.intro hAfterCacheHidden (And.intro hAfterCacheNew hAfterCacheFrame)
    · have hOldOwned := hAfterCacheOldUpdates hZero
      have hOldRoot := hOldOwned.buffer.rootBound
      have hOldRoot32 : oldUpdates.root.toNat ≤ 4294967296 := by have := hOldOwned.buffer.addressBound; omega
      have hInputRoot := hAfterCacheInput.buffer.rootBound
      have hInputRoot32 : inputNode.root.toNat ≤ 4294967296 := by have := hAfterCacheInput.buffer.addressBound; omega
      have hh := (hAfterCacheHidden.released oldUpdates hOldRoot hOldRoot32 (hHiddenOldUpdates hZero)).released
        inputNode hInputRoot hInputRoot32 hHiddenInput
      have hu := (hAfterCacheNew.released oldUpdates hOldRoot hOldRoot32 (hNewOldUpdates hZero)).released
        inputNode hInputRoot hInputRoot32 hNewInput
      have hf := (hAfterCacheFrame.released oldUpdates hOldRoot hOldRoot32 (hUpdatesFresh hZero)).released
        inputNode hInputRoot hInputRoot32 (hInputFresh hZero)
      simpa only [finalStore, stepHeap, cacheReleasedHeap, appendHeap, updatesNode, oldReleaseHeap, oldReleaseStore, hZero, ite_false] using And.intro hh (And.intro hu hf)
  apply advanceLayer_spec env _ _ embeddingPtr inputNode.root oldUpdates.root (CachedBlock.hiddenNode heap position).root
    (updatesNode heap position layer).root layer updates.size preparedFrame rfl hLayer hPrepared
  intro result hResult
  apply hNext _ result hResult hFinalHeap hFinal.1 hFinal.2.1 hFinal.2.2
    (hBefore.freshNode hHiddenFresh) (hBeforeBlock.freshNode hNewFresh) (regionsDisjoint_symm hNewHidden)
  · by_cases hZero : layer = 0 <;>
      simpa only [oldReleaseStore, hZero, ite_true, ite_false, Heap.releaseStore, releasedStore_pages] using hAppendOutput.pages
  · by_cases hZero : layer = 0 <;>
      simpa only [oldReleaseStore, hZero, ite_true, ite_false, Heap.releaseStore, releasedStore_memoryCap] using
        (hAppendOutput.memoryCap «module» 0).trans hBlockCap

#print axioms layerStep_spec

end Project.Gpt2CachedStep.CachedHidden
