import Project.Drone.ExecutionUnwindFrame
import Project.Drone.ExecutionRead

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
theorem unwind_speed_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel index state : Nat) (terrain history row : UInt64) (tracked : Bool)
    (out0 out1 : UInt64) (aux : List Value) (s : Scratch) (hAux : aux.length = 36)
    (hState : state < UInt64.size) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ nextAux : List Value, nextAux.length = 36 → nextAux[35]? = aux[35]? →
      wp Project.Drone.«module» rest Q store
        (unwindFrame fuel index state terrain history row tracked out0 out1 nextAux
          { s with source := row, value := speed state }) env) :
    wp Project.Drone.«module» ((unwindLoopBody.drop 7).take 11 ++ rest) Q store
      (unwindFrame fuel index state terrain history row tracked out0 out1 aux s) env := by
  simp only [unwindLoopBody, func24, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.take, List.cons_append, List.nil_append]
  wp_unwind_frame [hAux]
  refine wp_call_tw (speed_exact env store state hState) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_unwind_frame [hAux, func10Def]
  apply hNext <;> simp [hAux]

set_option maxRecDepth 32768 in
theorem unwind_altitude_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel index state : Nat) (terrain history row root : UInt64) (tracked : Bool)
    (out0 out1 : UInt64) (aux : List Value) (s : Scratch) (heights : Array UInt64)
    (hAux : aux.length = 36) (hTerrain : UInt64Array.At store terrain heights)
    (hIndex : index < heights.size) (hState : state < UInt64.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ nextAux : List Value, nextAux.length = 36 → nextAux[35]? = aux[35]? →
      wp Project.Drone.«module» rest Q store
        (unwindFrame fuel index state terrain history row tracked out0 out1 nextAux
          { s with source := root, value := altitude (floorAt heights index) state }) env) :
    wp Project.Drone.«module» ((unwindLoopBody.drop 85).take 24 ++ rest) Q store
      { unwindFrame fuel index state terrain history row tracked out0 out1 aux s with values := [.i64 root] } env := by
  simp only [unwindLoopBody, func24, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.take, List.cons_append, List.nil_append]
  wp_unwind_frame [hAux]
  refine wp_call_tw (floorAt_exact env store 0 terrain heights index hTerrain hIndex) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_unwind_frame [hAux, func20Def]
  refine wp_call_tw (altitude_exact env _ (floorAt heights index) state hState) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_unwind_frame [hAux, func4Def]
  apply hNext <;> simp [hAux]

#print axioms unwind_speed_spec
#print axioms unwind_altitude_spec
end Project.Drone.Execution
