import Project.Drone.ExecutionComputeFrame
import Project.ProofKit.NatSub

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxRecDepth 32768 in
set_option maxHeartbeats 300000 in
theorem compute_unwind_prepare_spec (env : HostEnv Unit) (store : Store Unit) (terrain history : UInt64)
    (aux : List Value) (s : Scratch) (input : Array UInt64) (hAux : aux.length = 30)
    (hHistory0 : aux[18]? = some (.i64 history)) (hHistory1 : aux[19]? = some (.i64 history))
    (hInput : UInt64Array.At store terrain input) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ nextAux : List Value, nextAux.length = 30 →
      nextAux[20]? = some (.i64 (UInt64.ofNat input.size)) →
      nextAux[21]? = some (.i64 (UInt64.ofNat (input.size - 1))) →
      nextAux[22]? = some (.i64 0) → nextAux[23]? = some (.i64 0) →
      nextAux[24]? = some (.i64 terrain) → nextAux[25]? = some (.i64 history) → nextAux[26]? = some (.i64 history) →
      wp Project.Drone.«module» rest Q store
        (computeFrame terrain nextAux { s with counter := UInt64.ofNat input.size, value := 1, spare0 := terrain }) env) :
    wp Project.Drone.«module» ((computeAccept.drop 86).take 29 ++ rest) Q store (computeFrame terrain aux s) env := by
  have hRead := hInput.lengthRead
  have hAddress := hInput.pointerAddress_eq
  have hBound := Nat.not_lt.mpr hInput.lengthBound
  simp only [computeAccept, computeValidate, func25, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.drop, List.cons_append, List.nil_append]
  wp_compute_frame [hAux, hRead, hAddress, hBound, Nat.reducePow, UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero]
  refine NatSub.guard_spec 36 37 _ _ _ _ input.size 1 [] rfl ?_ ?_ hInput.size_lt (by decide) _ _ ?_
  · simp [Locals.get, hAux]
  · simp [Locals.get, hAux]
  wp_compute_frame [hAux, hHistory0, hHistory1]
  refine hNext _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [hAux]

#print axioms compute_unwind_prepare_spec
end Project.Drone.Execution
