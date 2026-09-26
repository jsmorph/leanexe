import Project.Gpt2QuantizedCached.CachedHidden.FinishAppend
import Project.Gpt2QuantizedCached.CachedHidden.FinishGuard
import Project.Gpt2QuantizedCached.CachedHidden.FinishMemory

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open Project.Gpt2CachedStep.LayerNorm (AllocationFits)

set_option maxRecDepth 32768 in
theorem emitted_finishBranchFull : (func58.drop 58).take 48 =
    finishPrepareCode ++ failureTestCode 105 ++ [.iff 0 0 finishFailureCode finishSuccessCode] := rfl

theorem finishBranch_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (params : List Value) (embedding updates hidden : FreeNode) (cachePtr : UInt64)
    (embeddingBytes updatesBytes hiddenBytes cache : ByteArray) (status : UInt64) (frame : Locals)
    (hParams : params.length = 8) (hCachePtr : params[4]? = some (.i64 cachePtr))
    (hCacheSize : params[5]? = some (.i64 (UInt64.ofNat cache.size)))
    (hHeap : heap.At initial) (hFrame : before.Frame original heap initial)
    (hCapacity : initial.memoryCap «module» 0 = original.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hEmbedding : heap.OwnsPacked initial embedding embeddingBytes)
    (hUpdates : heap.OwnsPacked initial updates updatesBytes)
    (hHidden : heap.StatusPacked initial status hidden hiddenBytes)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hEmbeddingFresh : before.FreshNode embedding) (hUpdatesFresh : before.FreshNode updates)
    (hHiddenFresh : status = 0 → before.FreshNode hidden)
    (hTemporarySep : regionsDisjoint updates.region embedding.region)
    (hHiddenEmbedding : status = 0 → regionsDisjoint hidden.region embedding.region)
    (hHiddenUpdates : status = 0 → regionsDisjoint hidden.region updates.region)
    (hSize : cache.size + updatesBytes.size ≤ 4294967296)
    (hFit : status = 0 → AllocationFits heap (PackedAppend.need cache updatesBytes) (initial.memoryCap «module» 0))
    (hState : LayerFrame params embedding.root (statusRoot status hidden) updates.root
      hiddenBytes.size updatesBytes.size status 12 frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      ResultFrame params embedding.root updates.root status (statusRoot status hidden)
        (statusRoot status (finishCacheNode heap cache updatesBytes))
        (finishValue status hiddenBytes cache updatesBytes).hidden.size
        (finishValue status hiddenBytes cache updatesBytes).cache.size result →
      FinishMemory before original (finishHeap heap status cache updatesBytes) final status
        embedding updates hidden (finishCacheNode heap cache updatesBytes) embeddingBytes updatesBytes
        (finishValue status hiddenBytes cache updatesBytes).hidden
        (finishValue status hiddenBytes cache updatesBytes).cache →
      wp «module» rest Q final result env) :
    wp «module» ((func58.drop 58).take 48 ++ rest) Q initial frame env := by
  rw [emitted_finishBranchFull]
  simp only [List.append_assoc]
  apply finishPrepare_spec env initial params embedding.root (statusRoot status hidden) updates.root
    hiddenBytes.size updatesBytes.size status frame hParams hState
  intro prepared hPrepared
  have hRead : prepared.get 105 = some (.i64 status) := by
    simpa [Locals.get, hPrepared.paramsEq, hParams, hPrepared.length] using hPrepared.status
  rw [← List.append_assoc (failureTestCode 105) [.iff 0 0 finishFailureCode finishSuccessCode]]
  apply failureGuard_spec env initial prepared 105 status hPrepared.values hRead
  by_cases hZero : status = 0
  · subst status
    rw [ite_eq_left rfl, emitted_finishSuccess]
    simp only [List.append_assoc]
    apply finishSuccessPrepare_spec env initial params embedding.root hidden.root updates.root cachePtr
      hiddenBytes.size updatesBytes.size cache.size prepared hParams hCachePtr hCacheSize hPrepared
    intro appendFrame hAppendFrame
    have hRun := finishAppend_spec env initial heap params embedding.root hidden.root updates.root cachePtr
      hiddenBytes.size updatesBytes cache appendFrame hHeap hUpdates.buffer.values hCache hUpdates.payload_protects
      hCacheProtected hSize (hFit rfl) hPages hParams hAppendFrame
      (PackedReleaseFilter.afterAction «module» env rest Q) []
    simp only [List.append_nil] at hRun
    apply hRun
    intro final result hResult hOutput
    simp only [wp_nil, PackedReleaseFilter.afterAction]
    have hEmpty : ({ result with values := [] } : Locals) = result := Frame.ext _ _ rfl rfl hResult.values.symm
    rw [hEmpty]
    apply hNext final result
    · simpa only [statusRoot, finishValue, ite_true, ByteArray.size_append, finishCacheNode, allocatedNode] using hResult
    · exact finishMemory_append before heap original initial final embedding updates hidden
        embeddingBytes updatesBytes hiddenBytes cache hEmbedding hUpdates (hHidden.owned rfl)
        hFrame hCapacity hEmbeddingFresh hUpdatesFresh (hHiddenFresh rfl) hTemporarySep
        (hHiddenEmbedding rfl) (hHiddenUpdates rfl) (fun h => (hFit rfl h).1.le) hOutput
  · rw [ite_eq_right hZero]
    have hRun := finishFailure_spec env initial params embedding.root (statusRoot status hidden) updates.root
      hiddenBytes.size updatesBytes.size status prepared hParams hPrepared
      (PackedReleaseFilter.afterAction «module» env rest Q) []
    simp only [List.append_nil] at hRun
    apply hRun
    intro result hResult
    simp only [wp_nil, PackedReleaseFilter.afterAction]
    have hEmpty : ({ result with values := [] } : Locals) = result := Frame.ext _ _ rfl rfl hResult.values.symm
    rw [hEmpty]
    apply hNext initial result
    · simpa only [statusRoot, finishValue, hZero, ite_false, ByteArray.size_empty] using hResult
    · simp only [finishHeap, finishValue, hZero, ite_false]
      refine ⟨Completion.failure before heap original initial status hidden _ hZero hHeap hFrame hPages hCapacity,
        hEmbedding, hUpdates, hEmbeddingFresh, hUpdatesFresh, hTemporarySep, ?_, ?_, ?_, ?_⟩
      all_goals intro h; exact False.elim (hZero h)

#print axioms finishBranch_spec
end Project.Gpt2QuantizedCached.CachedHidden
