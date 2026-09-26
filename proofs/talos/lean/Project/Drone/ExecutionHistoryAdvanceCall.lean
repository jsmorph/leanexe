import Project.Drone.ExecutionHistoryFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxRecDepth 32768 in
theorem history_advance_call_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel index : Nat) (terrain previous history out0 out1 seed r0 r1 : UInt64) (last : Bool)
    (aux : List Value) (s : Scratch) (hAux : aux.length = 44)
    (hCount : aux[1]? = some (.i64 45)) (hZero : aux[2]? = some (.i64 0))
    (hR0 : aux[7]? = some (.i64 r0)) (hR1 : aux[12]? = some (.i64 r1))
    (hLast : aux[13]? = some (.i64 (if last then 1 else 0)))
    (hOwner : aux[14]? = some (.i64 previous)) (hPointer : aux[15]? = some (.i64 previous))
    (P : Store Unit → UInt64 → Prop)
    (hCall : TerminatesWith env Project.Drone.«module» 18 store
      [.i64 seed, .i64 seed, .i64 previous, .i64 previous, .i64 (if last then 1 else 0),
        .i64 r1, .i64 r0, .i64 0, .i64 45]
      (fun final values => ∃ root : UInt64, values = [.i64 root, .i64 root] ∧ P final root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (root : UInt64) (nextAux : List Value),
      nextAux.length = 44 → nextAux[21]? = some (.i64 root) → nextAux[22]? = some (.i64 root) →
      P final root → wp Project.Drone.«module» rest Q final
        (historyFrame fuel index terrain previous history out0 out1 nextAux s) env) :
    wp Project.Drone.«module» ((historyLoopBody.drop 109).take 21 ++ rest) Q store
      { historyFrame fuel index terrain previous history out0 out1 aux s with values := [.i64 seed] } env := by
  simp only [historyLoopBody, func22, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.take, List.cons_append, List.nil_append]
  wp_history_frame [hAux, hCount, hZero, hR0, hR1, hLast, hOwner, hPointer]
  refine wp_call_tw hCall ?_
  rintro final values ⟨root, rfl, hP⟩
  wp_history_frame [hAux, func18Def]
  refine hNext final root _ ?_ ?_ ?_ hP <;> simp [hAux]

#print axioms history_advance_call_spec
end Project.Drone.Execution
