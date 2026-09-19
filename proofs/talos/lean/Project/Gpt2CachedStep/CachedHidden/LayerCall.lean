import Project.Gpt2CachedStep.CachedHidden.Code
import Project.Gpt2CachedStep.CachedHidden.Embedding

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def LayerState (params : List Value) (embeddingPtr inputPtr updatesPtr : UInt64)
    (layer updatesSize : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 119 ∧ frame.values = [] ∧ I64Values frame.locals ∧
  frame.locals[11]? = some (.i64 embeddingPtr) ∧ frame.locals[12]? = some (.i64 embeddingPtr) ∧
  frame.locals[13]? = some (.i64 3072) ∧
  frame.locals[17]? = some (.i64 inputPtr) ∧ frame.locals[18]? = some (.i64 inputPtr) ∧
  frame.locals[19]? = some (.i64 3072) ∧
  frame.locals[20]? = some (.i64 updatesPtr) ∧ frame.locals[21]? = some (.i64 updatesPtr) ∧
  frame.locals[22]? = some (.i64 (UInt64.ofNat updatesSize)) ∧
  frame.locals[95]? = some (.i64 (UInt64.ofNat layer)) ∧ frame.locals[96]? = some (.i64 12) ∧
  frame.locals[97]? = some (.i64 1) ∧ frame.locals[118]? = some (.i64 (if layer = 0 then 0 else 1))

def LayerCallState (params : List Value) (embeddingPtr inputPtr updatesPtr hiddenPtr cachePtr : UInt64)
    (layer updatesSize : Nat) (frame : Locals) : Prop :=
  LayerState params embeddingPtr inputPtr updatesPtr layer updatesSize frame ∧
  frame.locals[41]? = some (.i64 hiddenPtr) ∧ frame.locals[47]? = some (.i64 hiddenPtr) ∧
  frame.locals[53]? = some (.i64 hiddenPtr) ∧ frame.locals[54]? = some (.i64 hiddenPtr) ∧
  frame.locals[55]? = some (.i64 3072) ∧ frame.locals[44]? = some (.i64 cachePtr) ∧
  frame.locals[57]? = some (.i64 (UInt64.ofNat updatesSize)) ∧ frame.locals[59]? = some (.i64 6144) ∧
  frame.locals[98]? = some (.i64 updatesPtr) ∧ frame.locals[99]? = some (.i64 (UInt64.ofNat updatesSize)) ∧
  frame.locals[100]? = some (.i64 cachePtr) ∧ frame.locals[101]? = some (.i64 6144)

def layerCallCode : Wasm.Program :=
  [.localGet 103, .localSet 31,
   .localGet 25, .localSet 32, .localGet 26, .localSet 33, .localGet 27, .localSet 34,
   .localGet 29, .localSet 36, .localGet 30, .localSet 37,
   .localGet 0, .localSet 38, .localGet 1, .localSet 39, .localGet 2, .localSet 40,
   .localGet 32, .localSet 41, .localGet 33, .localSet 42, .localGet 34, .localSet 43,
   .localGet 3, .localSet 44, .localGet 4, .localSet 45, .localGet 5, .localSet 46,
   .localGet 31, .localSet 47, .localGet 7, .localSet 48,
   .localGet 38, .localGet 39, .localGet 40, .localGet 41, .localGet 42, .localGet 43,
   .localGet 44, .localGet 45, .localGet 46, .localGet 47, .localGet 48, .call 33,
   .localSet 54, .localSet 53, .localSet 52, .localSet 51, .localSet 50, .localSet 49,
   .localGet 49, .localSet 55, .localGet 50, .localSet 56, .localGet 51, .localSet 57,
   .localGet 53, .localSet 59, .localGet 54, .localSet 60,
   .localGet 55, .localSet 61, .localGet 56, .localSet 62, .localGet 57, .localSet 63,
   .localGet 36, .localSet 64, .localGet 37, .localSet 65, .localGet 59, .localSet 66, .localGet 60, .localSet 67,
   .localGet 64, .localSet 106, .localGet 65, .localSet 107, .localGet 66, .localSet 108, .localGet 67, .localSet 109]

set_option maxRecDepth 32768 in
theorem emitted_layerCall : (layerBody.drop 4).take 84 = layerCallCode := rfl

theorem layerCall_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr embeddingPtr inputPtr updatesPtr : UInt64)
    (weights input cache : ByteArray) (token : UInt32) (position layer updatesSize : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hLayer : layer < 12) (hPosition : position < 128)
    (hInputSize : input.size = 3072) (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hWeightsSize : (blocksOffset + layer * blockWords + blockWords) * 4 ≤ weights.size)
    (hResources : CachedBlock.Resources heap position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : LayerState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      embeddingPtr inputPtr updatesPtr layer updatesSize frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      LayerCallState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        embeddingPtr inputPtr updatesPtr (CachedBlock.hiddenNode heap position).root
        (CachedBlock.cacheNode heap position).root layer updatesSize result →
      (CachedBlock.finalHeap heap position).At final →
      (CachedBlock.finalHeap heap position).OwnsPacked final (CachedBlock.hiddenNode heap position)
        (cachedBlock weights input cache layer position).hidden →
      (CachedBlock.finalHeap heap position).OwnsPacked final (CachedBlock.cacheNode heap position)
        (cachedBlock weights input cache layer position).cache →
      heap.Frame initial (CachedBlock.finalHeap heap position) final →
      heap.FreshNode (CachedBlock.hiddenNode heap position) → heap.FreshNode (CachedBlock.cacheNode heap position) →
      regionsDisjoint (CachedBlock.hiddenNode heap position).region (CachedBlock.cacheNode heap position).region →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((layerBody.drop 4).take 84 ++ rest) Q initial frame env := by
  rcases hState with ⟨hParams, hLocals, hValues, hTyped, hEmbeddingOwner, hEmbeddingPtr, hEmbeddingSize,
    hInputOwner, hInputPtr, hInputBytes, hUpdatesOwner, hUpdatesPtr, hUpdatesBytes,
    hCounter, hLimit, hStep, hOld⟩
  have hCall := CachedBlock.Spec.cachedBlock_exact env initial heap weightsOwner inputPtr cacheOwner
    weightsPtr inputPtr cachePtr weights input cache layer position hHeap hWeights hInput hCache
    hWeightsProtected hInputProtected hCacheProtected hLayer hPosition hInputSize hCacheSize hWeightsSize hResources hPages
  simp only [hInputSize] at hCall
  rw [emitted_layerCall]
  simp only [layerCallCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hInputOwner, hInputPtr, hInputBytes,
    hUpdatesPtr, hUpdatesBytes, hCounter]
  refine wp_call_tw hCall ?_
  rintro final values ⟨hReturned, hFinalHeap, hHidden, hCache, hFrame, hHiddenFresh, hCacheFresh, hSeparated, hFinalPages, hCapacity⟩
  rw [CachedBlock.Spec.cachedBlock_hidden_size _ _ _ _ _ hInputSize,
    CachedBlock.Spec.cachedBlock_cache_size] at hReturned
  subst values
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [LayerCallState, LayerState, parameters, hLocals,
      List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      hEmbeddingOwner, hEmbeddingPtr, hEmbeddingSize, hInputOwner, hInputPtr, hInputBytes,
      hUpdatesOwner, hUpdatesPtr, hUpdatesBytes, hCounter, hLimit, hStep, hOld,
      I64Values.set, hTyped, UInt64.ofNat_uInt32ToNat,
      show UInt64.ofNat 3072 = 3072 from rfl, show UInt64.ofNat 6144 = 6144 from rfl, and_self]
  · exact hFinalHeap
  · exact hHidden
  · exact hCache
  · exact hFrame
  · exact hHiddenFresh
  · exact hCacheFresh
  · exact hSeparated
  · exact hFinalPages
  · exact hCapacity

#print axioms layerCall_spec

end Project.Gpt2CachedStep.CachedHidden
