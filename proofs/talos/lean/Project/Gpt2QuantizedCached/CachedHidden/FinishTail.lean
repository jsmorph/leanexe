import Project.Gpt2QuantizedCached.CachedHidden.Cleanup
import Project.Gpt2QuantizedCached.CachedHidden.FinishPlan

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

def resultValues (status : UInt64) (hidden cache : FreeNode) (hiddenSize cacheSize : Nat) : List Value :=
  [.i64 (UInt64.ofNat cacheSize), .i64 (statusRoot status cache), .i64 (statusRoot status cache),
   .i64 (UInt64.ofNat hiddenSize), .i64 (statusRoot status hidden), .i64 (statusRoot status hidden), .i64 status]

set_option maxRecDepth 32768 in
theorem emitted_finishTail : func58.drop 106 =
    finishUpdatesReleaseCode ++ finishEmbeddingReleaseCode ++
    [.localGet 111, .localGet 112, .localGet 113, .localGet 114, .localGet 115, .localGet 116, .localGet 117] := rfl

theorem finishTail_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (params : List Value) (embedding updates hidden cache : FreeNode)
    (embeddingBytes updatesBytes hiddenBytes cacheBytes : ByteArray) (status : UInt64) (frame : Locals)
    (hParams : params.length = 8)
    (hMemory : FinishMemory before original heap initial status embedding updates hidden cache
      embeddingBytes updatesBytes hiddenBytes cacheBytes)
    (hState : ResultFrame params embedding.root updates.root status (statusRoot status hidden)
      (statusRoot status cache) hiddenBytes.size cacheBytes.size frame)
    (Q : Assertion Unit)
    (hNext : ∀ final result,
      result.values = resultValues status hidden cache hiddenBytes.size cacheBytes.size →
      Completion before original (cleanedHeap heap embedding updates) final
        status hidden cache hiddenBytes cacheBytes → Q (.Fallthrough final result)) :
    wp «module» (func58.drop 106) Q initial frame env := by
  rw [emitted_finishTail]
  apply cleanup_spec env original initial before heap params embedding updates hidden cache
    embeddingBytes updatesBytes hiddenBytes cacheBytes status frame hParams hMemory.toCompletion hState
    hMemory.embeddingOwned hMemory.updatesOwned hMemory.embeddingFresh hMemory.updatesFresh
    hMemory.temporarySep hMemory.hiddenEmbedding hMemory.hiddenUpdates hMemory.cacheEmbedding hMemory.cacheUpdates
  intro hCompletion
  wp_packed_frame [hState.paramsEq, hParams, hState.length, hState.values, hState.status,
    hState.hiddenOwner, hState.hiddenPtr, hState.hiddenSize, hState.cacheOwner, hState.cachePtr, hState.cacheSize]
  exact hNext _ _ rfl hCompletion

#print axioms finishTail_spec
end Project.Gpt2QuantizedCached.CachedHidden
