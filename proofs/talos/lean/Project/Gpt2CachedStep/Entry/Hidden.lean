import Project.Gpt2CachedStep.Entry.Code

namespace Project.Gpt2CachedStep.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def hiddenCode : Wasm.Program :=
  [.constI64 0, .localSet 6, .localGet 0, .localSet 7, .localGet 1, .localSet 8,
   .constI64 0, .localSet 9, .localGet 2, .localSet 10, .localGet 3, .localSet 11,
   .localGet 4, .constI64 4294967295, .andI64, .localSet 12, .localGet 5, .localSet 13,
   .localGet 6, .localGet 7, .localGet 8, .localGet 9, .localGet 10, .localGet 11, .localGet 12, .localGet 13, .call 36,
   .localSet 19, .localSet 18, .localSet 17, .localSet 16, .localSet 15, .localSet 14,
   .localGet 14, .localSet 20, .localGet 15, .localSet 21, .localGet 16, .localSet 22,
   .localGet 17, .localSet 23, .localGet 18, .localSet 24, .localGet 19, .localSet 25]

set_option maxRecDepth 32768 in
theorem emitted_hidden : validBody.take 45 = hiddenCode := rfl

theorem hidden_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsPtr cachePtr : UInt64) (weights cache : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hValid : Valid weights cache token position)
    (hResources : CachedHidden.Resources heap position cache.size (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : State (parameters weightsPtr cachePtr weights cache token position) frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      HiddenState (parameters weightsPtr cachePtr weights cache token position)
        (CachedHidden.traversed heap position).hidden.root (CachedHidden.cacheNode heap position cache.size).root
        (cache.size + 73728) result →
      (CachedHidden.finalHeap heap position cache.size).At final →
      (CachedHidden.finalHeap heap position cache.size).OwnsPacked final (CachedHidden.traversed heap position).hidden
        (cachedHidden weights cache token position).hidden →
      (CachedHidden.finalHeap heap position cache.size).OwnsPacked final (CachedHidden.cacheNode heap position cache.size)
        (cachedHidden weights cache token position).cache →
      heap.Frame initial (CachedHidden.finalHeap heap position cache.size) final →
      heap.FreshNode (CachedHidden.traversed heap position).hidden → heap.FreshNode (CachedHidden.cacheNode heap position cache.size) →
      regionsDisjoint (CachedHidden.traversed heap position).hidden.region (CachedHidden.cacheNode heap position cache.size).region →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» (validBody.take 45 ++ rest) Q initial frame env := by
  rcases hState with ⟨hParams, hLocals, hValues, hTyped⟩
  have hExtents := valid_extents hValid
  have hCall := CachedHidden.Spec.cachedHidden_exact env initial heap 0 weightsPtr 0 cachePtr weights cache token position
    hHeap hWeights hCache hWeightsProtected hCacheProtected hValid.2.1 hValid.2.2.1
    hExtents.1 hExtents.2.1 hExtents.2.2.1 hExtents.2.2.2.1 hExtents.2.2.2.2 hResources hPages
  simp only [UInt64.ofNat_uInt32ToNat] at hCall
  rw [emitted_hidden]
  simp only [hiddenCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, PackedFloatFrame.mask]
  refine wp_call_tw hCall ?_
  rintro final values ⟨hReturned, hFinalHeap, hHidden, hCache, hFrame, hHiddenFresh, hCacheFresh, hSeparated, hFinalPages, hCapacity⟩
  rw [CachedHidden.Spec.cachedHidden_hidden_size, CachedHidden.Spec.cachedHidden_cache_size] at hReturned
  subst values
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [HiddenState, State, parameters, hLocals,
      List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hTyped, show UInt64.ofNat 3072 = 3072 from rfl, and_self]
  · exact hFinalHeap
  · exact hHidden
  · exact hCache
  · exact hFrame
  · exact hHiddenFresh
  · exact hCacheFresh
  · exact hSeparated
  · exact hFinalPages
  · exact hCapacity

#print axioms hidden_spec

end Project.Gpt2CachedStep.Entry
