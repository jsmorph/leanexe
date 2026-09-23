import Project.Gpt2QuantizedCached.CachedHidden.CacheRelease

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem emitted_activeCode : activeCode = layerCallCode ++ PackedAppend.program 130 ++
    layerResultCode ++ cacheReleaseCode := rfl

theorem activeBranch_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr embeddingPtr inputPtr updatesPtr : UInt64)
    (weights input cache updates : ByteArray) (token : UInt32) (position layer : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hUpdates : ByteArrayAt initial.mem updatesPtr.toNat updates)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hUpdatesProtected : heap.Protects updatesPtr.toNat (updatesPtr.toNat + updates.size))
    (hLayer : layer < 12) (hPosition : position < 128)
    (hExtent : blocksOffset + layer * blockBytes + blockBytes ≤ weights.size)
    (hInputSize : input.size = 3072) (hUpdatesSize : updates.size ≤ layer * 6144)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hResources : LayerResources heap position (CachedBlock.tensors weights input cache layer position)
      updates (cachedBlock weights input cache layer position) (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : PreparedFrame (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      embeddingPtr inputPtr updatesPtr input.size updates.size 0 layer frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      let output := cachedBlock weights input cache layer position
      let values := CachedBlock.tensors weights input cache layer position
      SelectedFrame (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        embeddingPtr inputPtr updatesPtr (statusRoot output.status (CachedBlock.hiddenNode heap position))
        (updatesNode heap position values updates output).root input.size updates.size 0 layer
        output.hidden.size (updates.size + output.cache.size) output.status result →
      PendingOutput heap initial (cacheReleasedHeap heap position values updates output)
        final output.status (CachedBlock.hiddenNode heap position)
        (updatesNode heap position values updates output) output.hidden (updates ++ output.cache) →
      wp «module» rest Q final result env) :
    wp «module» (activeCode ++ rest) Q initial frame env := by
  rw [emitted_activeCode]
  simp only [List.append_assoc]
  apply layerCall_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr embeddingPtr inputPtr updatesPtr
    weights input cache token position layer updates.size 0 frame hHeap hWeights hInput hCache
    hWeightsProtected hInputProtected hCacheProtected hLayer hPosition hExtent hInputSize hCacheSize
    hResources.block hPages hState
  intro blockStore blockFrame
  dsimp only
  intro hCall hBlock
  have hPacked := hBlock.sourcePacked weights input cache layer position hInputSize
  have hAppendFit : Project.Gpt2CachedStep.LayerNorm.AllocationFits
      (CachedBlock.executionHeap heap position (CachedBlock.tensors weights input cache layer position))
      (PackedAppend.need updates (cachedBlock weights input cache layer position).cache)
      (blockStore.memoryCap «module» 0) := by
    rw [hBlock.memoryCap]
    exact hResources.append
  have hSize : updates.size + (cachedBlock weights input cache layer position).cache.size ≤ 4294967296 :=
    (Nat.add_le_add hUpdatesSize (CachedBlock.cachedBlock_cache_le weights input cache layer position hInputSize)).trans
      (by omega)
  rw [← List.append_assoc (PackedAppend.program 130) layerResultCode]
  apply layerAppend_spec env blockStore
    (CachedBlock.executionHeap heap position (CachedBlock.tensors weights input cache layer position))
    _ embeddingPtr inputPtr updatesPtr
    (statusRoot (cachedBlock weights input cache layer position).status (CachedBlock.hiddenNode heap position))
    (statusRoot (cachedBlock weights input cache layer position).status (CachedBlock.cacheNode heap position))
    input.size updates 0 layer (cachedBlock weights input cache layer position) blockFrame hBlock.heapAt
    (hBlock.frame.packed hUpdatesProtected hUpdates) hPacked.2.values
    (hBlock.frame.protects _ _ hUpdatesProtected) hPacked.2.protects hSize hAppendFit hBlock.pages rfl hCall
  intro appendStore appendFrame hAppState hAppend
  have hMemory := appendedMemory heap initial blockStore appendStore weights input cache updates layer position
    hInputSize hBlock (fun h => (hAppendFit h).1.le) hAppend
  apply cacheRelease_spec env initial appendStore heap
    (appendedHeap heap position (CachedBlock.tensors weights input cache layer position) updates
      (cachedBlock weights input cache layer position))
    _ embeddingPtr inputPtr updatesPtr input.size updates 0 layer (CachedBlock.hiddenNode heap position)
    (updatesNode heap position (CachedBlock.tensors weights input cache layer position) updates
      (cachedBlock weights input cache layer position))
    (CachedBlock.cacheNode heap position) (cachedBlock weights input cache layer position) appendFrame
    rfl hMemory hAppState
  intro final result hSelected hOutput
  exact hNext final result hSelected hOutput

#print axioms activeBranch_spec
end Project.Gpt2QuantizedCached.CachedHidden
