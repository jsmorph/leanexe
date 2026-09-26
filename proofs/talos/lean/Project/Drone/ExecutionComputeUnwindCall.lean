import Project.Drone.ExecutionComputeFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxRecDepth 32768 in
theorem compute_unwind_call_spec (env : HostEnv Unit) (store : Store Unit) (terrain history seed : UInt64)
    (count : Nat) (aux : List Value) (s : Scratch) (hAux : aux.length = 30)
    (hCount : aux[20]? = some (.i64 (UInt64.ofNat count)))
    (hIndex : aux[21]? = some (.i64 (UInt64.ofNat (count - 1))))
    (hState : aux[22]? = some (.i64 0)) (hOwner : aux[23]? = some (.i64 0))
    (hTerrain : aux[24]? = some (.i64 terrain))
    (hHistory0 : aux[25]? = some (.i64 history)) (hHistory1 : aux[26]? = some (.i64 history))
    (P : Store Unit → UInt64 → Prop)
    (hCall : TerminatesWith env Project.Drone.«module» 24 store
      [.i64 seed, .i64 seed, .i64 history, .i64 history, .i64 terrain, .i64 0, .i64 0,
        .i64 (UInt64.ofNat (count - 1)), .i64 (UInt64.ofNat count)]
      (fun final values => ∃ root, values = [.i64 root, .i64 root] ∧ P final root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (root : UInt64) (nextAux : List Value), nextAux.length = 30 → P final root →
      wp Project.Drone.«module» rest Q final
        (computeFrame terrain nextAux { s with source := root, length := root, nextLength := root, target := root }) env) :
    wp Project.Drone.«module» (computeAccept.drop 155 ++ rest) Q store
      { computeFrame terrain aux s with values := [.i64 seed] } env := by
  simp only [computeAccept, computeValidate, func25, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.cons_append, List.nil_append]
  wp_compute_frame [hAux, hCount, hIndex, hState, hOwner, hTerrain, hHistory0, hHistory1]
  refine wp_call_tw hCall ?_
  rintro final values ⟨root, rfl, hP⟩
  wp_compute_frame [hAux, func24Def]
  refine hNext final root _ ?_ hP
  simp [hAux]

#print axioms compute_unwind_call_spec
end Project.Drone.Execution
