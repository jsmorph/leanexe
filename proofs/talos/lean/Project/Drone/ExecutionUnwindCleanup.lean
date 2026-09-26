import Project.Drone.ExecutionUnwindFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxRecDepth 32768 in
set_option maxHeartbeats 300000 in
theorem unwind_cleanup_spec (env : HostEnv Unit) (store final : Store Unit)
    (fuel index state nextIndex nextState : Nat) (terrain history row root : UInt64) (tracked : Bool)
    (out0 out1 : UInt64) (aux : List Value) (s : Scratch) (hAux : aux.length = 36)
    (hIndex : aux[15]? = some (.i64 (UInt64.ofNat nextIndex)))
    (hState : aux[16]? = some (.i64 (UInt64.ofNat nextState)))
    (hTerrain0 : aux[17]? = some (.i64 terrain)) (hTerrain1 : aux[18]? = some (.i64 terrain))
    (hHistory0 : aux[19]? = some (.i64 history)) (hHistory1 : aux[20]? = some (.i64 history))
    (hRoot0 : aux[21]? = some (.i64 root)) (hRoot1 : aux[22]? = some (.i64 root))
    (hTerrain : terrain ≠ 0) (hHistory : history ≠ 0) (hRow : row ≠ 0)
    (hOldTerrain : row ≠ terrain) (hOldHistory : row ≠ history) (hOldRoot : row ≠ root)
    (hUntracked : tracked = false → final = store)
    (hRelease : tracked = true → TerminatesWith env Project.Drone.«module» 29 store [.i64 row]
      (fun released values => released = final ∧ values = []))
    (Q : Assertion Unit)
    (hNext : ∀ nextAux : List Value, nextAux.length = 36 → nextAux[33]? = some (.i64 0) → nextAux[35]? = aux[35]? →
      Q (.Break 0 final (unwindFrame fuel nextIndex nextState terrain history root true out0 out1 nextAux s))) :
    wp Project.Drone.«module» (unwindLoopBody.drop 207) Q store
      (unwindFrame (fuel + 1) index state terrain history row tracked out0 out1 aux s) env := by
  have hSub : UInt64.ofNat (fuel + 1) - 1 = UInt64.ofNat fuel := by
    rw [UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl, UInt64.add_sub_cancel]
  simp only [unwindLoopBody, func24, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop]
  cases tracked with
  | false =>
    have hFinal := hUntracked rfl
    subst final
    unwind_controls [hAux, hIndex, hState, hTerrain0, hTerrain1, hHistory0, hHistory1,
      hRoot0, hRoot1, hTerrain, hHistory, hSub]
    apply hNext <;> simp [hAux]
  | true =>
    unwind_controls [hAux, hIndex, hState, hTerrain0, hTerrain1, hHistory0, hHistory1,
      hRoot0, hRoot1, hTerrain, hHistory, hRow, hOldTerrain, hOldHistory, hOldRoot, hSub]
    refine wp_call_tw (hRelease rfl) ?_
    rintro released values ⟨rfl, rfl⟩
    unwind_controls [hAux, hIndex, hState, hTerrain0, hTerrain1, hHistory0, hHistory1,
      hRoot0, hRoot1, hTerrain, hHistory, hRow, hOldTerrain, hOldHistory, hOldRoot, hSub,
      Ne.symm hOldTerrain, Ne.symm hOldHistory, func29Def]
    apply hNext <;> simp [hAux]

#print axioms unwind_cleanup_spec
end Project.Drone.Execution
