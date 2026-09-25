import Project.Gpt2CachedStep.CachedHidden.CacheAppend
import Project.ProofKit.PackedReleaseFilter

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

def cleanupItems (embeddingNode : FreeNode) (embeddingBytes : ByteArray) : List PackedReleaseMany.Item :=
  [⟨19, embeddingNode, embeddingBytes⟩]

set_option maxRecDepth 32768 in
theorem emitted_cleanup (embeddingNode : FreeNode) (embeddingBytes : ByteArray) :
    func36.drop 169 = PackedReleaseFilter.program 83 [19, 100, 97] [.localGet 83, .call 42] ++
      PackedReleaseMany.program (cleanupItems embeddingNode embeddingBytes) 100 97 42 ++
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
    hHiddenOwner, hHiddenPtr, hHiddenSize, hCacheOwner, hCachePtr, hCacheSize, _⟩
  have hReadEmbedding : frame.get 19 = some (.i64 embeddingNode.root) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hEmbeddingBinding
  have hReadUpdates : frame.get 83 = some (.i64 updatesNode.root) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hUpdatesBinding
  have hReadHidden : frame.get 97 = some (.i64 hiddenNode.root) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hHiddenOwner
  have hReadCache : frame.get 100 = some (.i64 cacheNode.root) := by
    simpa [Locals.get, hParams, hParamsLength, hLocals] using hCacheOwner
  have hRoot := hUpdates.buffer.rootBound
  have hRoot32 : updatesNode.root.toNat ≤ 4294967296 := by
    have := hUpdates.buffer.addressBound
    omega
  have hRootNe : updatesNode.root ≠ 0 := by
    intro hZero
    rw [hZero] at hRoot
    contradiction
  have hRetainedNe : ∀ entry ∈ [(19, embeddingNode.root), (100, cacheNode.root), (97, hiddenNode.root)],
      updatesNode.root ≠ entry.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hUpdates.root_ne hTemporarySep, hUpdates.root_ne hUpdatesCache, hUpdates.root_ne hUpdatesHidden⟩
  rw [emitted_cleanup embeddingNode embeddingBytes]
  simp only [List.append_assoc]
  apply PackedReleaseFilter.program_spec «module» env initial frame 83 updatesNode.root
    [(19, embeddingNode.root), (100, cacheNode.root), (97, hiddenNode.root)]
    [.localGet 83, .call 42] hValues hReadUpdates
  · intro entry hEntry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hEntry
    rcases hEntry with rfl | rfl | rfl
    · exact hReadEmbedding
    · exact hReadCache
    · exact hReadHidden
  · intro _
    simp only [Locals.get] at hReadUpdates
    wp_packed_frame [hValues, hReadUpdates]
    refine wp_call_tw (heap.releasePacked_exact env «module» 42 initial updatesNode updatesBytes
      (typeIdx := some 42) rfl rfl hHeap hUpdates) ?_
    rintro final values ⟨rfl, rfl, hReleased⟩
    simp only [wp_nil, PackedReleaseFilter.afterAction]
    have hEmpty : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hValues.symm
    rw [hEmpty]
    apply PackedReleaseMany.program_spec env «module» 42 (heap.releaseStore initial updatesNode)
      (heap.release updatesNode) before original frame
      (cleanupItems embeddingNode embeddingBytes) cacheNode hiddenNode cacheBytes hiddenBytes
      100 97 (typeIdx := some 42) rfl rfl hReleased
    · simpa [cleanupItems] using hEmbedding.released updatesNode hRoot hRoot32 (regionsDisjoint_symm hTemporarySep)
    · exact hCache.released updatesNode hRoot hRoot32 (regionsDisjoint_symm hUpdatesCache)
    · exact hHidden.released updatesNode hRoot hRoot32 (regionsDisjoint_symm hUpdatesHidden)
    · simp [cleanupItems]
    · simpa [cleanupItems] using hEmbeddingCache
    · simpa [cleanupItems] using hEmbeddingHidden
    · exact hFrame.released updatesNode hRoot hRoot32 hUpdatesFresh
    · simpa [cleanupItems, Heap.FreshNode] using hEmbeddingFresh
    · exact hValues
    · simpa [cleanupItems] using hReadEmbedding
    · exact hReadCache
    · exact hReadHidden
    intro hFinalHeap hFinalCache hFinalHidden hFinalFrame
    wp_packed_frame [hParams, hParamsLength, hLocals, hValues, hHiddenOwner, hHiddenPtr, hHiddenSize,
      hCacheOwner, hCachePtr, hCacheSize]
    exact hNext _ hFinalHeap hFinalHidden hFinalCache hFinalFrame rfl
  · intro hSkip
    exact False.elim (hSkip ⟨hRootNe, hRetainedNe⟩)

#print axioms cleanup_spec

end Project.Gpt2CachedStep.CachedHidden
