import Project.Drone.ExecutionComputeFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxRecDepth 32768 in
theorem compute_history_call_spec (env : HostEnv Unit) (store : Store Unit) (terrain previous seed : UInt64)
    (count : Nat) (aux : List Value) (s : Scratch) (hAux : aux.length = 30)
    (hCount : aux[5]? = some (.i64 (UInt64.ofNat count))) (hIndex : aux[6]? = some (.i64 1))
    (hOwner : aux[7]? = some (.i64 0)) (hTerrain : aux[8]? = some (.i64 terrain))
    (hPrev0 : aux[11]? = some (.i64 previous)) (hPrev1 : aux[12]? = some (.i64 previous))
    (P : Store Unit → UInt64 → Prop)
    (hCall : TerminatesWith env Project.Drone.«module» 22 store
      [.i64 seed, .i64 seed, .i64 previous, .i64 previous, .i64 terrain, .i64 0, .i64 1, .i64 (UInt64.ofNat count)]
      (fun final values => ∃ root, values = [.i64 root, .i64 root] ∧ P final root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (root : UInt64) (nextAux : List Value), nextAux.length = 30 →
      nextAux[18]? = some (.i64 root) → nextAux[19]? = some (.i64 root) → P final root →
      wp Project.Drone.«module» rest Q final (computeFrame terrain nextAux s) env) :
    wp Project.Drone.«module» ((computeAccept.drop 66).take 20 ++ rest) Q store
      { computeFrame terrain aux s with values := [.i64 seed] } env := by
  simp only [computeAccept, computeValidate, func25, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.drop, List.cons_append, List.nil_append]
  wp_compute_frame [hAux, hCount, hIndex, hOwner, hTerrain, hPrev0, hPrev1]
  refine wp_call_tw hCall ?_
  rintro final values ⟨root, rfl, hP⟩
  wp_compute_frame [hAux, func22Def]
  refine hNext final root _ ?_ ?_ ?_ hP <;> simp [hAux]

#print axioms compute_history_call_spec
end Project.Drone.Execution
