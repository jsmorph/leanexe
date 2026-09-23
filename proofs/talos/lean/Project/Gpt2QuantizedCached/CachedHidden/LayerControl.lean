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

def breakFrame (frame : Locals) : Locals :=
  { frame with locals := (frame.locals.set 78 (.i64 0)).set 87 (.i64 0), values := [] }

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
   .localGet 86,
   .localSet 95]

def layerAdvanceCode : Program :=
  [.localGet 79,
   .localSet 144,
   .localGet 80,
   .localSet 145,
   .localGet 81,
   .localSet 146,
   .localGet 82,
   .localSet 147,
   .localGet 83,
   .localSet 148,
   .localGet 84,
   .localSet 149,
   .localGet 85,
   .localSet 150,
   .localGet 95,
   .localSet 143,
   .localGet 144,
   .localSet 23,
   .localGet 145,
   .localSet 24,
   .localGet 146,
   .localSet 25,
   .localGet 147,
   .localSet 26,
   .localGet 148,
   .localSet 27,
   .localGet 149,
   .localSet 28,
   .localGet 150,
   .localSet 29,
   .constI64 1,
   .localSet 151,
   .localGet 143,
   .constI64 0,
   .neI64,
   .br_if 1,
   .localGet 127,
   .localSet 130,
   .localGet 129,
   .localSet 131,
   .localGet 130,
   .localGet 131,
   .addI64,
   .localTee 132,
   .localGet 130,
   .ltUI64,
   .iff 0 1 [
     .unreachable
    ] [
     .localGet 132
    ] [] [.i64],
   .localSet 127]

theorem emitted_layerBreak : (layerBody.drop 39).take 14 = layerBreakCode := rfl

theorem emitted_layerAdvance : (layerBody.drop 72).take 48 = layerAdvanceCode := rfl

theorem layerBreak_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (status : UInt64) (hParams : frame.params.length = 8) (hLocals : frame.locals.length = 144)
    (hValues : frame.values = []) (hRead : frame.locals[21]? = some (.i64 status))
    (Q : Assertion Unit) (rest : Program)
    (hNext : wp «module» rest Q store (breakFrame frame) env) :
    wp «module» (layerBreakCode ++ rest) Q store frame env := by
  have hCode : layerBreakCode = statusTestCode 29 ++
      [.iff 0 1 [.constI64 0] [.constI64 0] [] [.i64],
       .localSet 86, .localGet 86, .localSet 95] := rfl
  rw [hCode, List.append_assoc]
  apply statusTest_spec env store frame 29 status hValues
    (by simpa [Locals.get, hParams, hLocals] using hRead)
  simp only [List.cons_append, List.nil_append, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases h : status = 0
  all_goals
    simp only [h, ite_true, ite_false]
    first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    wp_packed_frame [hParams, hLocals]
    exact hNext

theorem layerAdvance_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (params : List Value) (embedding input updates hidden newUpdates : UInt64)
    (inputBytes updateBytes : Nat) (inputStatus : UInt64) (layer hiddenBytes newUpdateBytes : Nat)
    (newStatus : UInt64) (hParams : params.length = 8) (hLayer : layer < 12)
    (hState : SelectedFrame params embedding input updates hidden newUpdates inputBytes updateBytes
      inputStatus layer hiddenBytes newUpdateBytes newStatus frame)
    (hBreak : frame.locals[87]? = some (.i64 0))
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result,
      LayerFrame params embedding hidden newUpdates hiddenBytes newUpdateBytes newStatus (layer + 1) result →
      wp «module» rest Q store result env) :
    wp «module» (layerAdvanceCode ++ rest) Q store frame env := by
  have hSafe := CheckedNatAdd.guard_of_fits layer 1 (by change _ < 18446744073709551616; omega)
  have hAdd : UInt64.ofNat layer + 1 = UInt64.ofNat (layer + 1) := by simp
  simp only [layerAdvanceCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, hParams, hState.length, hState.values,
    hState.outputHiddenOwner, hState.outputHiddenPtr, hState.outputHiddenSize,
    hState.outputUpdatesOwner, hState.outputUpdatesPtr, hState.outputUpdatesSize,
    hState.outputStatus, hBreak, hState.counter, hState.step]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hSafe)]
  wp_packed_frame [hState.paramsEq, hParams, hState.length, hAdd]
  apply hNext
  constructor <;>
    simp (config := { maxDischargeDepth := 64 }) only [hState.length, List.length_set,
      List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte, I64Values.set, hState.typed,
      hState.embeddingOwner, hState.embeddingPtr, hState.embeddingSize,
      hState.protectedEmbedding, hState.protectedUpdates, hState.limit, hState.step,
      show layer + 1 ≠ 0 by omega, ite_false]

#print axioms layerBreak_spec
#print axioms layerAdvance_spec
end Project.Gpt2QuantizedCached.CachedHidden
