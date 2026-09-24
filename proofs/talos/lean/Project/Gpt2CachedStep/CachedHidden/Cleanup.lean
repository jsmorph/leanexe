import Project.Gpt2CachedStep.CachedHidden.CacheAppend
import Project.ProofKit.PackedReleaseManyAliases

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

def cleanupItems (embeddingNode updatesNode : FreeNode) (embeddingBytes updatesBytes : ByteArray) : List PackedReleaseMany.Item :=
  [⟨83, updatesNode, updatesBytes⟩, ⟨19, embeddingNode, embeddingBytes⟩]

def cleanupKept (owner : Nat) : List Nat :=
  if owner = 83 then [97, 100, 24, 23, 22, 20, 19] else [97, 100]

set_option maxRecDepth 32768 in
theorem emitted_cleanup (embeddingNode updatesNode : FreeNode) (embeddingBytes updatesBytes : ByteArray) :
    func36.drop 169 = PackedReleaseManyAliases.program (cleanupItems embeddingNode updatesNode embeddingBytes updatesBytes) cleanupKept 42 ++
      [.localGet 97, .localGet 98, .localGet 99, .localGet 100, .localGet 101, .localGet 102] := rfl

theorem cleanup_spec (env : HostEnv Unit) (initial original : Store Unit) (heap before : Heap)
    (params : List Value) (embeddingNode updatesNode hiddenNode cacheNode : FreeNode)
    (embeddingBytes updatesBytes hiddenBytes cacheBytes : ByteArray) (frame : Locals)
    (hHeap : heap.At initial)
    (hEmbedding : heap.OwnsPacked initial embeddingNode embeddingBytes)
    (hUpdates : heap.OwnsPacked initial updatesNode updatesBytes)
    (hHidden : heap.OwnsPacked initial hiddenNode hiddenBytes)
    (hCache : heap.OwnsPacked initial cacheNode cacheBytes)
    (hTemporarySep : regionsDisjoint updatesNode.region embeddingNode.region)
    (hEmbeddingHidden : regionsDisjoint embeddingNode.region hiddenNode.region)
    (hUpdatesHidden : regionsDisjoint updatesNode.region hiddenNode.region)
    (hEmbeddingCache : regionsDisjoint embeddingNode.region cacheNode.region)
    (hUpdatesCache : regionsDisjoint updatesNode.region cacheNode.region)
    (hFrame : before.Frame original heap initial)
    (hEmbeddingFresh : before.FreshNode embeddingNode) (hUpdatesFresh : before.FreshNode updatesNode)
    (hParamsLength : params.length = 8)
    (hState : HiddenResultState params embeddingNode.root updatesNode.root hiddenNode.root cacheNode.root cacheBytes.size frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result,
      (heap.release updatesNode |>.release embeddingNode).At
        ((heap.release updatesNode).releaseStore (heap.releaseStore initial updatesNode) embeddingNode) →
      (heap.release updatesNode |>.release embeddingNode).OwnsPacked
        ((heap.release updatesNode).releaseStore (heap.releaseStore initial updatesNode) embeddingNode) hiddenNode hiddenBytes →
      (heap.release updatesNode |>.release embeddingNode).OwnsPacked
        ((heap.release updatesNode).releaseStore (heap.releaseStore initial updatesNode) embeddingNode) cacheNode cacheBytes →
      before.Frame original (heap.release updatesNode |>.release embeddingNode)
        ((heap.release updatesNode).releaseStore (heap.releaseStore initial updatesNode) embeddingNode) →
      result.values = [.i64 (UInt64.ofNat cacheBytes.size), .i64 cacheNode.root, .i64 cacheNode.root,
        .i64 3072, .i64 hiddenNode.root, .i64 hiddenNode.root] →
      wp «module» rest Q ((heap.release updatesNode).releaseStore (heap.releaseStore initial updatesNode) embeddingNode) result env) :
    wp «module» (func36.drop 169 ++ rest) Q initial frame env := by
  rcases hState with ⟨hParams, hLocals, hValues, _, hEmbeddingBinding, hUpdatesBinding,
    hHiddenOwner, hHiddenPtr, hHiddenSize, hCacheOwner, hCachePtr, hCacheSize,
    hEmbeddingPtr, hEmptyOwner, hEmptyPtr, hEmptySize⟩
  have hReadEmbedding : frame.get 19 = some (.i64 embeddingNode.root) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hEmbeddingBinding
  have hReadUpdates : frame.get 83 = some (.i64 updatesNode.root) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hUpdatesBinding
  have hReadHidden : frame.get 97 = some (.i64 hiddenNode.root) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hHiddenOwner
  have hReadCache : frame.get 100 = some (.i64 cacheNode.root) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hCacheOwner
  have hReadEmbeddingPtr : frame.get 20 = some (.i64 embeddingNode.root) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hEmbeddingPtr
  have hRead22 : frame.get 22 = some (.i64 0) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hEmptyOwner
  have hRead23 : frame.get 23 = some (.i64 0) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hEmptyPtr
  have hRead24 : frame.get 24 = some (.i64 0) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hEmptySize
  have hUpdatesNonzero : updatesNode.root ≠ 0 := by
    intro hZero
    have := hUpdates.buffer.rootBound
    simp [hZero] at this
  rw [emitted_cleanup embeddingNode updatesNode embeddingBytes updatesBytes, List.append_assoc]
  apply PackedReleaseManyAliases.program_spec env «module» 42 initial heap before original frame
    (cleanupItems embeddingNode updatesNode embeddingBytes updatesBytes) cacheNode hiddenNode cacheBytes hiddenBytes
    cleanupKept (typeIdx := some 42) rfl rfl hHeap
  · simpa [cleanupItems] using And.intro hUpdates hEmbedding
  · exact hCache
  · exact hHidden
  · simpa [cleanupItems] using hTemporarySep
  · simpa [cleanupItems] using And.intro hUpdatesCache hEmbeddingCache
  · simpa [cleanupItems] using And.intro hUpdatesHidden hEmbeddingHidden
  · exact hFrame
  · simpa [cleanupItems, Heap.FreshNode] using And.intro hUpdatesFresh hEmbeddingFresh
  · exact hValues
  · simpa [cleanupItems] using And.intro hReadUpdates hReadEmbedding
  · intro item hItem slot hSlot
    simp only [cleanupItems, List.mem_cons, List.not_mem_nil, or_false] at hItem
    rcases hItem with rfl | rfl
    · simp only [cleanupKept, reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hSlot
      rcases hSlot with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hiddenNode.root, hReadHidden, hUpdates.root_ne hUpdatesHidden⟩
      · exact ⟨cacheNode.root, hReadCache, hUpdates.root_ne hUpdatesCache⟩
      · exact ⟨0, hRead24, hUpdatesNonzero⟩
      · exact ⟨0, hRead23, hUpdatesNonzero⟩
      · exact ⟨0, hRead22, hUpdatesNonzero⟩
      · exact ⟨embeddingNode.root, hReadEmbeddingPtr, hUpdates.root_ne hTemporarySep⟩
      · exact ⟨embeddingNode.root, hReadEmbedding, hUpdates.root_ne hTemporarySep⟩
    · simp only [cleanupKept, Nat.reduceEqDiff, reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hSlot
      rcases hSlot with rfl | rfl
      · exact ⟨hiddenNode.root, hReadHidden, hEmbedding.root_ne hEmbeddingHidden⟩
      · exact ⟨cacheNode.root, hReadCache, hEmbedding.root_ne hEmbeddingCache⟩
  intro hFinalHeap hFinalCache hFinalHidden hFinalFrame
  simp only [List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hParamsLength, hLocals, hValues, hHiddenOwner, hHiddenPtr, hHiddenSize,
    hCacheOwner, hCachePtr, hCacheSize]
  exact hNext _ hFinalHeap hFinalHidden hFinalCache hFinalFrame rfl

#print axioms cleanup_spec

end Project.Gpt2CachedStep.CachedHidden
