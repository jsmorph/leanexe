import Project.Drone.ExecutionAppendFrame
import Project.ProofKit.CheckedNatAdd

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxHeartbeats 200000 in
set_option maxRecDepth 32768 in
theorem append_read_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel state : Nat) (layerOwner layerPointer historyOwner historyPointer
      tracker resultOwner resultPointer : UInt64) (aux : List Value) (s : Scratch) (extra : UInt64)
    (layer : Array UInt64) (hAux : aux.length = 14)
    (hLayer : UInt64Array.At store layerPointer layer) (hRead : 3 * state + 2 < layer.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.Drone.«module» rest Q store
      (appendFrame fuel state layerOwner layerPointer historyOwner historyPointer tracker resultOwner
        resultPointer (appendPreparedAux aux state layerOwner layerPointer historyPointer)
        (appendPreparedScratch s state layerPointer historyPointer layer[3 * state + 2])
        (UInt64.ofNat state)) env) :
    wp Project.Drone.«module» ((appendBody.drop 7).take 48 ++ rest) Q store
      (appendFrame fuel state layerOwner layerPointer historyOwner historyPointer tracker resultOwner
        resultPointer aux s extra) env := by
  have hSize := hLayer.size_lt
  have hState : state < UInt64.size := by omega
  have hNextState : state + 1 < UInt64.size := by omega
  have hIndex : 3 * state + 2 < UInt64.size := by omega
  simp only [appendBody, func21, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.drop, List.take, List.cons_append, List.nil_append]
  wp_append_frame [hAux]
  refine CheckedNatAdd.guard_spec 27 _ _ _ _ state 1 [] rfl ?_ hNextState _ _ ?_
  · simp [Locals.get, hAux, UInt64.ofNat_add]
  wp_append_frame [hAux]
  change wp _ (CheckedNatMul.guardProgram 39 40 ++ _) _ _ _ _
  refine CheckedNatMul.guard_spec 39 40 _ _ _ _ 3 (UInt64.ofNat state) [] rfl ?_ ?_ ?_ _ _ ?_
  · simp [Locals.get, hAux]
  · simp [Locals.get, hAux]
  · simpa only [UInt64.toNat_ofNat_of_lt' hState, show (3 : UInt64).toNat = 3 from rfl] using
      (show 3 * state < UInt64.size by omega)
  wp_append_frame [hAux]
  refine CheckedNatAdd.guard_spec 38 _ _ _ _ (3 * state) 2 [] ?_ ?_ hIndex _ _ ?_
  · simp only [UInt64.ofNat_mul, show UInt64.ofNat 3 = 3 from rfl, show UInt64.ofNat 2 = 2 from rfl]
  · simp [Locals.get, hAux, UInt64.ofNat_add, UInt64.ofNat_mul]
  wp_fixed_frame_step
  simp only [List.length_append, List.length_set, List.length_cons, List.length_nil,
    hAux, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, List.set_append, Nat.reduceSub, List.set]
  change wp _ (CheckedArrayGet.checkedGetCore 34 35 ++ _) _ _ _ _
  refine CheckedArrayGet.checkedGetCore_spec 34 35 _ _ _ _ layerPointer layer (3 * state + 2) []
    ?_ ?_ rfl hLayer hRead _ _ ?_
  · simp [Locals.get, hAux]
  · simp [Locals.get, hAux, UInt64.ofNat_add, UInt64.ofNat_mul]
  wp_append_frame [hAux]
  simpa only [appendFrame, appendPreparedAux, appendPreparedScratch, Scratch.words,
    UInt64.ofNat_add, UInt64.ofNat_mul, show UInt64.ofNat 1 = 1 from rfl,
    show UInt64.ofNat 2 = 2 from rfl, show UInt64.ofNat 3 = 3 from rfl,
    List.cons_append, List.nil_append] using hNext

#print axioms append_read_spec
end Project.Drone.Execution
