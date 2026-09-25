import Project.Gpt2QuantizedCached.CachedHidden.ActiveBranch
import Project.Gpt2QuantizedCached.CachedHidden.ActiveTail
import Project.Gpt2QuantizedCached.CachedHidden.InactiveStep

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem activeStep_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (embedding inputNode oldUpdates : FreeNode)
    (embeddingBytes weights input cache updates : ByteArray) (token : UInt32) (position layer : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hBefore : before.Frame original heap initial)
    (hCapacity : initial.memoryCap «module» 0 = original.memoryCap «module» 0)
    (hEmbedding : before.OwnsPacked original embedding embeddingBytes)
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
    (hInputZero : layer = 0 → inputNode.root = embedding.root)
    (hUpdatesZero : layer = 0 → oldUpdates.root = 0)
    (hOldSeparated : layer ≠ 0 → regionsDisjoint inputNode.region oldUpdates.region)
    (hLayer : layer < 12) (hPosition : position < 128)
    (hInputSize : input.size = 3072) (hUpdatesSize : updates.size = layer * 6144)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hExtent : blocksOffset + layer * blockBytes + blockBytes ≤ weights.size)
    (hResources : LayerResources heap position (CachedBlock.tensors weights input cache layer position)
      updates (cachedBlock weights input cache layer position) (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : LayerFrame (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      embedding.root inputNode.root oldUpdates.root input.size updates.size 0 layer frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      let output := cachedBlock weights input cache layer position
      let values := CachedBlock.tensors weights input cache layer position
      LayerFrame (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        embedding.root (statusRoot output.status (CachedBlock.hiddenNode heap position))
        (updatesNode heap position values updates output).root
        output.hidden.size (updates.size + output.cache.size) output.status (layer + 1) result →
      PendingOutput before original (activeHeap heap inputNode oldUpdates position layer values updates output)
        final output.status (CachedBlock.hiddenNode heap position)
        (updatesNode heap position values updates output) output.hidden (updates ++ output.cache) →
      wp «module» rest Q final result env) :
    wp «module» ((layerBody.drop 4).take 137 ++ rest) Q initial frame env := by
  rw [emitted_layerStep]
  simp only [List.append_assoc]
  apply layerPrepare_spec env initial _ embedding.root inputNode.root oldUpdates.root input.size updates.size
    0 layer frame rfl hState
  intro prepared hPrepared
  have hRead : prepared.get 41 = some (.i64 0) := by
    simpa [Locals.get, hPrepared.paramsEq, parameters, hPrepared.length] using hPrepared.statusCopy
  rw [← List.append_assoc (statusTestCode 41) [.iff 0 0 activeCode inactiveCode]]
  apply statusGuard_spec env initial prepared 41 0 hPrepared.values hRead
  rw [ite_eq_left rfl]
  have hRun := activeBranch_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr
    embedding.root inputNode.root oldUpdates.root weights input cache updates token position layer prepared
    hHeap hWeights hInput.buffer.values ⟨inputNode, rfl, hInput⟩
    (by
      by_cases hZero : layer = 0
      · exact Or.inl (hUpdatesZero hZero)
      · exact Or.inr ⟨oldUpdates, rfl, hUpdatesOwned hZero⟩)
    hCache hUpdates hWeightsProtected hInput.payload_protects
    hCacheProtected hUpdatesProtected hLayer hPosition hExtent hInputSize hUpdatesSize.le hCacheSize
    hResources hPages hPrepared
    (PackedReleaseFilter.afterAction «module» env
      (layerBreakCode ++ (updatesReleaseCode ++ (hiddenReleaseCode ++ (layerAdvanceCode ++ rest)))) Q) []
  apply (List.append_nil activeCode) ▸ hRun
  intro branchStore branchFrame
  dsimp only
  intro hSelected hMemory
  simp only [wp_nil, PackedReleaseFilter.afterAction]
  have hEmpty : ({ branchFrame with values := [] } : Locals) = branchFrame :=
    Frame.ext _ _ rfl rfl hSelected.values.symm
  rw [hEmpty]
  have hSelected' : SelectedFrame
      (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      embedding.root inputNode.root oldUpdates.root
      (statusRoot (cachedBlock weights input cache layer position).status (CachedBlock.hiddenNode heap position))
      (updatesNode heap position (CachedBlock.tensors weights input cache layer position) updates
        (cachedBlock weights input cache layer position)).root
      input.size updates.size 0 layer (cachedBlock weights input cache layer position).hidden.size
      (updates ++ (cachedBlock weights input cache layer position).cache).size
      (cachedBlock weights input cache layer position).status branchFrame := by
    simpa only [ByteArray.size_append] using hSelected
  apply activeTail_spec env original initial branchStore before heap _ _ embedding inputNode oldUpdates
    (CachedBlock.hiddenNode heap position)
    (updatesNode heap position (CachedBlock.tensors weights input cache layer position) updates
      (cachedBlock weights input cache layer position))
    embeddingBytes input updates (cachedBlock weights input cache layer position).hidden
    (updates ++ (cachedBlock weights input cache layer position).cache)
    (cachedBlock weights input cache layer position).status layer branchFrame rfl hLayer hMemory hBefore hCapacity
    hEmbedding hInput hUpdatesOwned hInputFresh hUpdatesFresh hInputZero hUpdatesZero hUpdatesSize hOldSeparated hSelected'
  intro final result hResult hOutput
  apply hNext final result
  · simpa only [ByteArray.size_append] using hResult
  · exact hOutput

#print axioms activeStep_spec
end Project.Gpt2QuantizedCached.CachedHidden
