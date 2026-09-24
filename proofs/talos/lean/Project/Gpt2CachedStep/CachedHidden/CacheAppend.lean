import Project.Gpt2CachedStep.CachedHidden.CachePrepare

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def HiddenResultState (params : List Value) (embeddingPtr updatesPtr hiddenPtr cachePtr : UInt64)
    (cacheSize : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 124 ∧ frame.values = [] ∧ I64Values frame.locals ∧
  frame.locals[11]? = some (.i64 embeddingPtr) ∧ frame.locals[75]? = some (.i64 updatesPtr) ∧
  frame.locals[89]? = some (.i64 hiddenPtr) ∧ frame.locals[90]? = some (.i64 hiddenPtr) ∧
  frame.locals[91]? = some (.i64 3072) ∧
  frame.locals[92]? = some (.i64 cachePtr) ∧ frame.locals[93]? = some (.i64 cachePtr) ∧
  frame.locals[94]? = some (.i64 (UInt64.ofNat cacheSize)) ∧
  frame.locals[12]? = some (.i64 embeddingPtr) ∧
  frame.locals[14]? = some (.i64 0) ∧ frame.locals[15]? = some (.i64 0) ∧ frame.locals[16]? = some (.i64 0)

def cacheAppendTail : Wasm.Program :=
  [.localSet 100, .localGet 100, .localSet 101, .localGet 93, .localGet 95, .addI64, .localSet 102]

set_option maxRecDepth 32768 in
theorem emitted_cacheAppendFull : (func36.drop 122).take 47 = PackedAppend.program 103 ++ cacheAppendTail := rfl

theorem cacheAppend_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (embeddingPtr hiddenPtr updatesPtr cachePtr : UInt64)
    (cache updates : ByteArray) (frame : Locals)
    (hHeap : heap.At initial)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hUpdates : ByteArrayAt initial.mem updatesPtr.toNat updates)
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hUpdatesProtected : heap.Protects updatesPtr.toNat (updatesPtr.toNat + updates.size))
    (hSize : cache.size + updates.size ≤ 4294967296)
    (hResources : LayerNorm.AllocationFits heap (PackedAppend.need cache updates) (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536) (hParamsLength : params.length = 8)
    (hState : CachePreparedState params embeddingPtr hiddenPtr updatesPtr cachePtr cache.size updates.size frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result, HiddenResultState params embeddingPtr updatesPtr hiddenPtr
      (allocatedRoot heap.top (PackedAppend.need cache updates) heap.nodes) (cache.size + updates.size) result →
      heap.PackedOutput initial final (PackedAppend.need cache updates) (cache ++ updates) →
      wp «module» rest Q final result env) :
    wp «module» ((func36.drop 122).take 47 ++ rest) Q initial frame env := by
  rcases hState with ⟨hParams, hLocals, hValues, hTyped, hEmbedding, hUpdatesOwner, hHiddenOwner, hHiddenPtr,
    hHiddenSize, hCacheSize, hUpdatesSize, hLeftPtr, hLeftSize, hRightPtr, hRightSize, hEmbeddingPtr, hEmptyOwner, hEmptyPtr, hEmptySize⟩
  have hParamLength : frame.params.length = 8 := by rw [hParams, hParamsLength]
  rw [emitted_cacheAppendFull, List.append_assoc]
  apply PackedAppend.program_spec 103 «module» env initial heap frame cachePtr updatesPtr cache updates
    hHeap hCache hUpdates hCacheProtected hUpdatesProtected hSize hResources hPages rfl
    (by rw [hParamLength]; decide) (by rw [hParamLength, hLocals]; decide) hValues hTyped
  · simpa [Locals.get, hParamLength, hLocals] using hLeftPtr
  · simpa [Locals.get, hParamLength, hLocals] using hLeftSize
  · simpa [Locals.get, hParamLength, hLocals] using hRightPtr
  · simpa [Locals.get, hParamLength, hLocals] using hRightSize
  intro final result hReturned hPreserved hOutput
  have hResultParams : result.params = params := hPreserved.1.trans hParams
  have hResultLength : result.locals.length = 124 := hPreserved.2.1.trans hLocals
  have hRead (index : Nat) (hi : index < 95) : result.locals[index]? = frame.locals[index]? :=
    hPreserved.local index (by rw [hParamLength]; omega)
  have hAdd : UInt64.ofNat cache.size + UInt64.ofNat updates.size = UInt64.ofNat (cache.size + updates.size) := by simp
  simp only [cacheAppendTail, List.cons_append, List.nil_append]
  wp_packed_frame [hResultParams, hParamsLength, hResultLength, hReturned,
    hRead 85 (by decide), hRead 87 (by decide), hCacheSize, hUpdatesSize, hAdd]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [HiddenResultState, hResultLength,
      List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hPreserved.2.2.1,
      hRead 11 (by decide), hRead 12 (by decide), hRead 14 (by decide), hRead 15 (by decide), hRead 16 (by decide), hRead 75 (by decide), hRead 89 (by decide), hRead 90 (by decide), hRead 91 (by decide),
      hEmbedding, hEmbeddingPtr, hEmptyOwner, hEmptyPtr, hEmptySize, hUpdatesOwner, hHiddenOwner, hHiddenPtr, hHiddenSize, and_self]
  · exact hOutput

#print axioms cacheAppend_spec

end Project.Gpt2CachedStep.CachedHidden
