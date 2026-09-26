import Project.Drone.ExecutionComputeFrame
import Project.Drone.ExecutionValidation

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
set_option maxHeartbeats 300000 in
theorem compute_validate_spec (env : HostEnv Unit) (store : Store Unit) (terrain : UInt64)
    (aux : List Value) (s : Scratch) (input : Array UInt64) (hAux : aux.length = 30)
    (hInput : UInt64Array.At store terrain input) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ nextAux : List Value, nextAux.length = 30 →
      wp Project.Drone.«module» rest Q store
        { computeFrame terrain nextAux { s with counter := terrain } with
          values := [.i32 (if validHeights input.size input then 1 else 0)] } env) :
    wp Project.Drone.«module» (computeValidate.take 22 ++ rest) Q store (computeFrame terrain aux s) env := by
  have hRead := hInput.lengthRead
  have hAddress := hInput.pointerAddress_eq
  have hBound := Nat.not_lt.mpr hInput.lengthBound
  simp only [computeValidate, func25, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.cons_append, List.nil_append]
  wp_compute_frame [hAux, hRead, hAddress, hBound, Nat.reducePow, UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero]
  refine wp_call_tw (validHeights_exact env store 0 terrain input input.size hInput le_rfl) ?_
  rintro final values ⟨rfl, rfl⟩
  cases hValid : validHeights input.size input
  all_goals
    simp only [hValid, Bool.false_eq_true, ↓reduceIte] at hNext
    compute_controls [hAux, func0Def, boolWord, hValid]
    simp
    apply hNext
    simp [hAux]

#print axioms compute_validate_spec
end Project.Drone.Execution
