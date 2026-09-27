import Project.Gpt2QuantizedCached.CachedHidden.LayerAppend
import Project.Gpt2QuantizedCached.CachedHidden.StatusGuard

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.ProofKit PackedFloatFrame

structure SelectedFrame (params : List Value) (embedding input updates hidden newUpdates : UInt64)
    (inputBytes updateBytes : Nat) (inputStatus : UInt64) (layer hiddenBytes newUpdateBytes : Nat)
    (newStatus : UInt64) (frame : Locals) : Prop
    extends LayerFrame params embedding input updates inputBytes updateBytes inputStatus layer frame where
  outputHiddenOwner : frame.locals[71]? = some (.i64 hidden)
  outputHiddenPtr : frame.locals[72]? = some (.i64 hidden)
  outputHiddenSize : frame.locals[73]? = some (.i64 (UInt64.ofNat hiddenBytes))
  outputUpdatesOwner : frame.locals[74]? = some (.i64 newUpdates)
  outputUpdatesPtr : frame.locals[75]? = some (.i64 newUpdates)
  outputUpdatesSize : frame.locals[76]? = some (.i64 (UInt64.ofNat newUpdateBytes))
  outputStatus : frame.locals[77]? = some (.i64 newStatus)

structure StagedFrame (params : List Value) (embedding input updates hidden newUpdates : UInt64)
    (inputBytes updateBytes : Nat) (inputStatus : UInt64) (layer hiddenBytes newUpdateBytes : Nat)
    (newStatus : UInt64) (frame : Locals) : Prop
    extends SelectedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
      inputStatus layer hiddenBytes newUpdateBytes newStatus frame where
  nextHiddenOwner : frame.locals[127]? = some (.i64 hidden)
  nextHiddenPtr : frame.locals[128]? = some (.i64 hidden)
  nextHiddenSize : frame.locals[129]? = some (.i64 (UInt64.ofNat hiddenBytes))
  nextUpdatesOwner : frame.locals[130]? = some (.i64 newUpdates)
  nextUpdatesPtr : frame.locals[131]? = some (.i64 newUpdates)
  nextUpdatesSize : frame.locals[132]? = some (.i64 (UInt64.ofNat newUpdateBytes))
  nextStatus : frame.locals[133]? = some (.i64 newStatus)
  done : frame.locals[126]? = some (.i64 0)

def layerBreakCode : Program :=
  [.localGet 29,
   .constI64 0,
   .eqI64,
   .iff 0 1 [
     .constI64 1
    ] [
     .constI64 0
    ] [] [.i64],
   .constI64 1,
   .eqI64,
   .iff 0 1 [
     .constI64 1
    ] [
     .constI64 0
    ] [] [.i64],
   .constI64 0,
   .eqI64,
   .eqz,
   .iff 0 1 [
     .constI64 0
    ] [
     .constI64 0
    ] [] [.i64],
   .localSet 86,
   .localGet 79,
   .localSet 135,
   .localGet 80,
   .localSet 136,
   .localGet 81,
   .localSet 137,
   .localGet 82,
   .localSet 138,
   .localGet 83,
   .localSet 139,
   .localGet 84,
   .localSet 140,
   .localGet 85,
   .localSet 141,
   .localGet 86,
   .localSet 134]

def layerAdvanceCode : Program :=
  [.localGet 135,
   .localSet 23,
   .localGet 136,
   .localSet 24,
   .localGet 137,
   .localSet 25,
   .localGet 138,
   .localSet 26,
   .localGet 139,
   .localSet 27,
   .localGet 140,
   .localSet 28,
   .localGet 141,
   .localSet 29,
   .localGet 134,
   .constI64 0,
   .neI64,
   .br_if 1,
   .localGet 118,
   .localSet 121,
   .localGet 120,
   .localSet 122,
   .localGet 121,
   .localGet 122,
   .addI64,
   .localTee 123,
   .localGet 121,
   .ltUI64,
   .iff 0 1 [
     .unreachable
    ] [
     .localGet 123
    ] [] [.i64],
   .localSet 118]

theorem emitted_layerBreak : (layerBody.drop 39).take 28 = layerBreakCode := rfl

theorem emitted_layerAdvance : (layerBody.drop 111).take 30 = layerAdvanceCode := rfl

theorem layerBreak_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (params : List Value) (embedding input updates hidden newUpdates : UInt64)
    (inputBytes updateBytes : Nat) (inputStatus : UInt64) (layer hiddenBytes newUpdateBytes : Nat)
    (newStatus : UInt64) (hParams : params.length = 8)
    (hState : SelectedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
      inputStatus layer hiddenBytes newUpdateBytes newStatus frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, StagedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
      inputStatus layer hiddenBytes newUpdateBytes newStatus result → wp «module» rest Q store result env) :
    wp «module» (layerBreakCode ++ rest) Q store frame env := by
  change wp «module» (statusTestCode 29 ++
    [.iff 0 1 [.constI64 0] [.constI64 0] [] [.i64], .localSet 86,
     .localGet 79, .localSet 135, .localGet 80, .localSet 136,
     .localGet 81, .localSet 137, .localGet 82, .localSet 138,
     .localGet 83, .localSet 139, .localGet 84, .localSet 140,
     .localGet 85, .localSet 141, .localGet 86, .localSet 134] ++ rest) Q store frame env
  rw [List.append_assoc]
  apply statusTest_spec env store frame 29 inputStatus hState.values
    (by simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.status)
  simp only [List.cons_append, List.nil_append, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  rw [ite_self]
  wp_packed_frame [hState.paramsEq, hParams, hState.length,
    hState.outputHiddenOwner, hState.outputHiddenPtr, hState.outputHiddenSize,
    hState.outputUpdatesOwner, hState.outputUpdatesPtr, hState.outputUpdatesSize, hState.outputStatus]
  apply hNext
  constructor
  · constructor
    · constructor <;>
        simp (config := { maxDischargeDepth := 64 }) only [hState.length, List.length_set,
          List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte, I64Values.set, hState.typed,
          hState.embeddingOwner, hState.embeddingPtr, hState.embeddingSize,
          hState.protectedEmbedding, hState.protectedUpdates, hState.hiddenOwner, hState.hiddenPtr,
          hState.hiddenSize, hState.updatesOwner, hState.updatesPtr, hState.updatesSize,
          hState.status, hState.counter, hState.limit, hState.step]
    all_goals simp only [List.getElem?_set, Nat.reduceEqDiff, reduceIte,
      hState.outputHiddenOwner, hState.outputHiddenPtr, hState.outputHiddenSize,
      hState.outputUpdatesOwner, hState.outputUpdatesPtr, hState.outputUpdatesSize, hState.outputStatus]
  all_goals simp only [hState.length, List.length_set, List.getElem?_set, Nat.reduceEqDiff,
    Nat.reduceLT, reduceIte]

theorem layerAdvance_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (params : List Value) (embedding input updates hidden newUpdates : UInt64)
    (inputBytes updateBytes : Nat) (inputStatus : UInt64) (layer hiddenBytes newUpdateBytes : Nat)
    (newStatus : UInt64) (hParams : params.length = 8) (hLayer : layer < 12)
    (hState : StagedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
      inputStatus layer hiddenBytes newUpdateBytes newStatus frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result,
      LayerFrame params embedding hidden newUpdates hiddenBytes newUpdateBytes newStatus (layer + 1) result →
      wp «module» rest Q store result env) :
    wp «module» (layerAdvanceCode ++ rest) Q store frame env := by
  have hSafe := CheckedNatAdd.guard_of_fits layer 1 (by change _ < 18446744073709551616; omega)
  have hAdd : UInt64.ofNat layer + 1 = UInt64.ofNat (layer + 1) := by simp
  simp only [layerAdvanceCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, hParams, hState.length, hState.values,
    hState.nextHiddenOwner, hState.nextHiddenPtr, hState.nextHiddenSize,
    hState.nextUpdatesOwner, hState.nextUpdatesPtr, hState.nextUpdatesSize,
    hState.nextStatus, hState.done, hState.counter, hState.step]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hSafe)]
  wp_packed_frame [hState.paramsEq, hParams, hState.length, hAdd]
  apply hNext
  constructor <;>
    simp (config := { maxDischargeDepth := 64 }) only [hState.length, List.length_set,
      List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte, I64Values.set, hState.typed,
      hState.embeddingOwner, hState.embeddingPtr, hState.embeddingSize,
      hState.protectedEmbedding, hState.protectedUpdates, hState.limit, hState.step]

#print axioms layerBreak_spec
#print axioms layerAdvance_spec
end Project.Gpt2QuantizedCached.CachedHidden
