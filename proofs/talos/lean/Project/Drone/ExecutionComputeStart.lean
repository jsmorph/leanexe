import Project.Drone.ExecutionComputeFrame
import Project.ProofKit.NatSub

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxRecDepth 32768 in
set_option maxHeartbeats 300000 in
theorem compute_start_spec (env : HostEnv Unit) (store : Store Unit) (terrain : UInt64)
    (aux : List Value) (s : Scratch) (input : Array UInt64) (hAux : aux.length = 30)
    (hInput : UInt64Array.At store terrain input) (P : Store Unit → UInt64 → Prop)
    (hCall : TerminatesWith env Project.Drone.«module» 23 store []
      (fun final values => ∃ root, values = [.i64 root, .i64 root] ∧ P final root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (root : UInt64) (nextAux : List Value), nextAux.length = 30 →
      nextAux[5]? = some (.i64 (UInt64.ofNat (input.size - 1))) → nextAux[6]? = some (.i64 1) →
      nextAux[7]? = some (.i64 0) → nextAux[8]? = some (.i64 terrain) →
      nextAux[11]? = some (.i64 root) → nextAux[12]? = some (.i64 root) → P final root →
      wp Project.Drone.«module» rest Q final
        (computeFrame terrain nextAux { s with counter := UInt64.ofNat input.size, value := 1, spare0 := terrain }) env) :
    wp Project.Drone.«module» (computeAccept.take 26 ++ rest) Q store (computeFrame terrain aux s) env := by
  have hRead := hInput.lengthRead
  have hAddress := hInput.pointerAddress_eq
  have hBound := Nat.not_lt.mpr hInput.lengthBound
  simp only [computeAccept, computeValidate, func25, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.cons_append, List.nil_append]
  wp_compute_frame [hAux, hRead, hAddress, hBound, Nat.reducePow, UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero]
  refine NatSub.guard_spec 36 37 _ _ _ _ input.size 1 [] rfl ?_ ?_ hInput.size_lt (by decide) _ _ ?_
  · simp [Locals.get, hAux]
  · simp [Locals.get, hAux]
  wp_compute_frame [hAux]
  refine wp_call_tw hCall ?_
  rintro final values ⟨root, rfl, hP⟩
  wp_compute_frame [hAux, func23Def]
  refine hNext final root _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hP <;> simp [hAux]

#print axioms compute_start_spec
end Project.Drone.Execution
