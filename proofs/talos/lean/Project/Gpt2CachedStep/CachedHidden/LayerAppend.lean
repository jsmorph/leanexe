import Project.Gpt2CachedStep.CachedHidden.LayerCall

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def LayerAppendState (params : List Value) (embeddingPtr inputPtr updatesPtr hiddenPtr cachePtr outputPtr : UInt64)
    (layer updatesSize : Nat) (frame : Locals) : Prop :=
  LayerState params embeddingPtr inputPtr updatesPtr layer updatesSize frame ∧
  frame.locals[41]? = some (.i64 hiddenPtr) ∧ frame.locals[44]? = some (.i64 cachePtr) ∧
  frame.locals[61]? = some (.i64 outputPtr) ∧
  frame.locals[64]? = some (.i64 hiddenPtr) ∧ frame.locals[65]? = some (.i64 hiddenPtr) ∧
  frame.locals[66]? = some (.i64 3072) ∧
  frame.locals[67]? = some (.i64 outputPtr) ∧ frame.locals[68]? = some (.i64 outputPtr) ∧
  frame.locals[69]? = some (.i64 (UInt64.ofNat (updatesSize + 6144))) ∧ frame.locals[70]? = some (.i64 0)

def layerAppendTail : Wasm.Program :=
  [.localSet 69, .localGet 69, .localSet 70, .localGet 65, .localGet 67, .addI64, .localSet 71,
   .localGet 61, .localSet 72, .localGet 62, .localSet 73, .localGet 63, .localSet 74,
   .localGet 69, .localSet 75, .localGet 70, .localSet 76, .localGet 71, .localSet 77,
   .constI64 0, .localSet 78]

set_option maxRecDepth 32768 in
theorem emitted_layerAppendFull : (layerBody.drop 88).take 61 = PackedAppend.program 106 ++ layerAppendTail := rfl

theorem layerAppend_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (embeddingPtr inputPtr updatesPtr hiddenPtr cachePtr : UInt64)
    (updates blockCache : ByteArray) (layer : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hUpdates : ByteArrayAt initial.mem updatesPtr.toNat updates)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat blockCache)
    (hUpdatesProtected : heap.Protects updatesPtr.toNat (updatesPtr.toNat + updates.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + blockCache.size))
    (hSize : updates.size + blockCache.size ≤ 4294967296) (hCacheSize : blockCache.size = 6144)
    (hBump : takeFirstFitFrom 0 (PackedAppend.need updates blockCache) heap.nodes = none →
      heap.top.toNat + 48 + (PackedAppend.need updates blockCache).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (PackedAppend.need updates blockCache) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) (hParamsLength : params.length = 8)
    (hState : LayerCallState params embeddingPtr inputPtr updatesPtr hiddenPtr cachePtr layer updates.size frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      LayerAppendState params embeddingPtr inputPtr updatesPtr hiddenPtr cachePtr
        (allocatedRoot heap.top (PackedAppend.need updates blockCache) heap.nodes) layer updates.size result →
      heap.PackedOutput initial final (PackedAppend.need updates blockCache) (updates ++ blockCache) →
      wp «module» rest Q final result env) :
    wp «module» ((layerBody.drop 88).take 61 ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨hParams, hLocals, hValues, hTyped, hEmbeddingOwner, hEmbeddingPtr, hEmbeddingSize,
    hInputOwner, hInputPtr, hInputBytes, hUpdatesOwner, hUpdatesPtr, hUpdatesBytes, hCounter, hLimit, hStep, hInitialInput, hInitialUpdates, hEmptyOwner, hEmptyPtr, hEmptySize⟩,
    hHidden49, hHidden55, hHiddenOwner, hHiddenPtr, hHiddenBytes, hCacheOwner, hOldSize, hBlockSize,
    hLeftPtr, hLeftSize, hRightPtr, hRightSize⟩
  have hParamLength : frame.params.length = 8 := by rw [hParams, hParamsLength]
  rw [emitted_layerAppendFull, List.append_assoc]
  apply PackedAppend.program_spec 106 «module» env initial heap frame updatesPtr cachePtr updates blockCache
    hHeap hUpdates hCache hUpdatesProtected hCacheProtected hSize hBump hPages rfl
    (by rw [hParamLength]; decide) (by rw [hParamLength, hLocals]; decide) hValues hTyped
  · simpa [Locals.get, hParamLength, hLocals] using hLeftPtr
  · simpa [Locals.get, hParamLength, hLocals] using hLeftSize
  · simpa [Locals.get, hParamLength, hLocals] using hRightPtr
  · simpa [Locals.get, hParamLength, hLocals, hCacheSize] using hRightSize
  intro final result hReturned hPreserved hOutput
  have hResultParams : result.params = params := hPreserved.1.trans hParams
  have hResultLength : result.locals.length = 124 := hPreserved.2.1.trans hLocals
  have hRead (index : Nat) (hi : index < 98 ∨ 111 ≤ index) : result.locals[index]? = frame.locals[index]? :=
    hPreserved.local index (by rw [hParamLength]; omega)
  have hAdd : UInt64.ofNat updates.size + 6144 = UInt64.ofNat (updates.size + 6144) := by simp
  simp only [layerAppendTail, List.cons_append, List.nil_append]
  wp_packed_frame [hResultParams, hParamsLength, hResultLength, hReturned,
    hRead 53 (by decide), hRead 54 (by decide), hRead 55 (by decide), hRead 57 (by decide), hRead 59 (by decide),
    hHiddenOwner, hHiddenPtr, hHiddenBytes, hOldSize, hBlockSize, hAdd]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [LayerAppendState, LayerState,
      hResultLength, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hPreserved.2.2.1,
      hRead 11 (by decide), hRead 12 (by decide), hRead 13 (by decide),
      hRead 17 (by decide), hRead 18 (by decide), hRead 19 (by decide),
      hRead 20 (by decide), hRead 21 (by decide), hRead 22 (by decide),
      hRead 95 (by decide), hRead 96 (by decide), hRead 97 (by decide), hRead 118 (by decide), hRead 121 (by decide),
      hRead 14 (by decide), hRead 15 (by decide), hRead 16 (by decide),
      hRead 41 (by decide), hRead 44 (by decide),
      hEmbeddingOwner, hEmbeddingPtr, hEmbeddingSize, hInputOwner, hInputPtr, hInputBytes,
      hUpdatesOwner, hUpdatesPtr, hUpdatesBytes, hCounter, hLimit, hStep, hInitialInput, hInitialUpdates, hEmptyOwner, hEmptyPtr, hEmptySize,
      hHidden49, hCacheOwner, and_self]
  · exact hOutput

#print axioms layerAppend_spec

end Project.Gpt2CachedStep.CachedHidden
