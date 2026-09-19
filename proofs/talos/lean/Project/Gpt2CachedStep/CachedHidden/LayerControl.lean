import Project.Gpt2CachedStep.CachedHidden.LayerAppend

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.ProofKit PackedFloatFrame

def initializeLayerCode : Wasm.Program :=
  [.constI64 0, .localSet 22, .constI64 0, .localSet 23, .constI64 0, .localSet 24,
   .constI64 0, .localSet 103, .constI64 12, .localSet 104, .constI64 1, .localSet 105,
   .localGet 19, .localSet 25, .localGet 20, .localSet 26, .localGet 21, .localSet 27,
   .localGet 22, .localSet 28, .localGet 23, .localSet 29, .localGet 24, .localSet 30,
   .constI64 0, .localSet 126]

set_option maxRecDepth 32768 in
theorem emitted_initializeLayer : (func36.drop 49).take 26 = initializeLayerCode := rfl

theorem initializeLayer_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (ptr : UInt64) (frame : Locals) (hParamsLength : params.length = 8)
    (hState : EmbeddingBuiltState params ptr frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, LayerState params ptr ptr 0 0 0 result → wp «module» rest Q store result env) :
    wp «module» ((func36.drop 49).take 26 ++ rest) Q store frame env := by
  rcases hState with ⟨⟨hParams, hLocals, hBytes, hTyped⟩, hValues, hOwner, hPtr, hSize⟩
  rw [emitted_initializeLayer]
  simp only [initializeLayerCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hParamsLength, hLocals, hValues, hOwner, hPtr, hSize]
  apply hNext
  simp (config := { maxDischargeDepth := 64 }) only [LayerState,
    hLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
    hOwner, hPtr, hSize, I64Values.set, hTyped, show UInt64.ofNat 0 = 0 from rfl, and_self]

def LayerPreparedState (params : List Value) (embeddingPtr inputPtr updatesPtr hiddenPtr outputPtr : UInt64)
    (layer updatesSize : Nat) (frame : Locals) : Prop :=
  LayerState params embeddingPtr inputPtr updatesPtr layer updatesSize frame ∧
  frame.locals[112]? = some (.i64 hiddenPtr) ∧ frame.locals[113]? = some (.i64 hiddenPtr) ∧
  frame.locals[114]? = some (.i64 3072) ∧
  frame.locals[115]? = some (.i64 outputPtr) ∧ frame.locals[116]? = some (.i64 outputPtr) ∧
  frame.locals[117]? = some (.i64 (UInt64.ofNat (updatesSize + 6144))) ∧ frame.locals[111]? = some (.i64 0)

def prepareLayerCode : Wasm.Program :=
  [.localGet 72, .localSet 120, .localGet 73, .localSet 121, .localGet 74, .localSet 122,
   .localGet 75, .localSet 123, .localGet 76, .localSet 124, .localGet 77, .localSet 125,
   .localGet 78, .localSet 119]

set_option maxRecDepth 32768 in
theorem emitted_prepareLayer : (layerBody.drop 173).take 14 = prepareLayerCode := rfl

theorem prepareLayer_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (embeddingPtr inputPtr updatesPtr hiddenPtr cachePtr outputPtr : UInt64) (layer updatesSize : Nat)
    (frame : Locals) (hParamsLength : params.length = 8)
    (hState : LayerAppendState params embeddingPtr inputPtr updatesPtr hiddenPtr cachePtr outputPtr layer updatesSize frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, LayerPreparedState params embeddingPtr inputPtr updatesPtr hiddenPtr outputPtr layer updatesSize result →
      wp «module» rest Q store result env) :
    wp «module» ((layerBody.drop 173).take 14 ++ rest) Q store frame env := by
  rcases hState with ⟨⟨hParams, hLocals, hValues, hTyped, hEmbeddingOwner, hEmbeddingPtr, hEmbeddingSize,
    hInputOwner, hInputPtr, hInputBytes, hUpdatesOwner, hUpdatesPtr, hUpdatesBytes, hCounter, hLimit, hStep, hOld⟩,
    _, _, _, hHiddenOwner, hHiddenPtr, hHiddenBytes, hOutputOwner, hOutputPtr, hOutputBytes, hBreak⟩
  rw [emitted_prepareLayer]
  simp only [prepareLayerCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hParamsLength, hLocals, hValues, hHiddenOwner, hHiddenPtr, hHiddenBytes,
    hOutputOwner, hOutputPtr, hOutputBytes, hBreak]
  apply hNext
  simp (config := { maxDischargeDepth := 64 }) only [LayerPreparedState, LayerState,
    hLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
    hEmbeddingOwner, hEmbeddingPtr, hEmbeddingSize, hInputOwner, hInputPtr, hInputBytes,
    hUpdatesOwner, hUpdatesPtr, hUpdatesBytes, hCounter, hLimit, hStep, hOld,
    I64Values.set, hTyped, and_self]

def advanceLayerCode : Wasm.Program :=
  [.localGet 120, .localSet 25, .localGet 121, .localSet 26, .localGet 122, .localSet 27,
   .localGet 123, .localSet 28, .localGet 124, .localSet 29, .localGet 125, .localSet 30,
   .constI64 1, .localSet 126, .localGet 119, .constI64 0, .neI64, .br_if 1,
   .localGet 103, .localSet 106, .localGet 105, .localSet 107,
   .localGet 106, .localGet 107, .addI64, .localTee 108, .localGet 106, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 108] [] [.i64], .localSet 103]

set_option maxRecDepth 32768 in
theorem emitted_advanceLayer : (layerBody.drop 191).take 30 = advanceLayerCode := rfl

theorem advanceLayer_spec (env : HostEnv Unit) (store : Store Unit) (params : List Value)
    (embeddingPtr inputPtr updatesPtr hiddenPtr outputPtr : UInt64) (layer updatesSize : Nat)
    (frame : Locals) (hParamsLength : params.length = 8) (hLayer : layer < 12)
    (hState : LayerPreparedState params embeddingPtr inputPtr updatesPtr hiddenPtr outputPtr layer updatesSize frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, LayerState params embeddingPtr hiddenPtr outputPtr (layer + 1) (updatesSize + 6144) result →
      wp «module» rest Q store result env) :
    wp «module» ((layerBody.drop 191).take 30 ++ rest) Q store frame env := by
  rcases hState with ⟨⟨hParams, hLocals, hValues, hTyped, hEmbeddingOwner, hEmbeddingPtr, hEmbeddingSize,
    _, _, _, _, _, _, hCounter, hLimit, hStep, _⟩,
    hHiddenOwner, hHiddenPtr, hHiddenBytes, hOutputOwner, hOutputPtr, hOutputBytes, hBreak⟩
  have hSafe := CheckedNatAdd.guard_of_fits layer 1 (by change _ < 18446744073709551616; omega)
  have hAdd : UInt64.ofNat layer + 1 = UInt64.ofNat (layer + 1) := by simp
  rw [emitted_advanceLayer]
  simp only [advanceLayerCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hParamsLength, hLocals, hValues, hHiddenOwner, hHiddenPtr, hHiddenBytes,
    hOutputOwner, hOutputPtr, hOutputBytes, hBreak, hCounter, hStep]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hSafe)]
  wp_packed_frame [hParams, hParamsLength, hLocals, hAdd]
  apply hNext
  simp (config := { maxDischargeDepth := 64 }) only [LayerState,
    hLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
    hEmbeddingOwner, hEmbeddingPtr, hEmbeddingSize, hLimit, hStep,
    I64Values.set, hTyped, show layer + 1 ≠ 0 by omega, ite_false, and_self]

#print axioms initializeLayer_spec
#print axioms prepareLayer_spec
#print axioms advanceLayer_spec

end Project.Gpt2CachedStep.CachedHidden
