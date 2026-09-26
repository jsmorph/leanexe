import Project.Drone.ExecutionAppendTail

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxHeartbeats 300000 in
set_option maxRecDepth 32768 in
theorem append_tail_release_spec (env : HostEnv Unit) (store final : Store Unit)
    (fuel state : Nat) (layerOwner layerPointer historyOwner historyPointer tracker
      resultOwner resultPointer root : UInt64) (aux : List Value) (s : Scratch) (extra : UInt64)
    (hAux : aux.length = 14) (hLayer : layerOwner ≠ 0) (hTracker : tracker ≠ 0)
    (hNew : tracker ≠ root) (hSeparate : tracker ≠ layerOwner)
    (hState : aux[0]? = some (.i64 (UInt64.ofNat (state + 1))))
    (hOwner : aux[1]? = some (.i64 layerOwner)) (hPointer : aux[2]? = some (.i64 layerPointer))
    (hRelease : TerminatesWith env Project.Drone.«module» 29 store [.i64 tracker]
      (fun released values => released = final ∧ values = []))
    (Q : Assertion Unit)
    (hNext : ∀ nextAux : List Value, nextAux.length = 14 →
      Q (.Break 0 final (appendFrame fuel (state + 1) layerOwner layerPointer root root root
        resultOwner resultPointer nextAux s extra))) :
    wp Project.Drone.«module» (appendBody.drop 122) Q store
      { appendFrame (fuel + 1) state layerOwner layerPointer historyOwner historyPointer tracker
          resultOwner resultPointer aux s extra with values := [.i64 root] } env := by
  have hSub : UInt64.ofNat (fuel + 1) - 1 = UInt64.ofNat fuel := by
    rw [UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl, UInt64.add_sub_cancel]
  simp only [appendBody, func21, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop]
  append_controls [hAux, hState, hOwner, hPointer, hLayer, hTracker, hNew, hSeparate, hSub]
  refine wp_call_tw hRelease ?_
  rintro released values ⟨rfl, rfl⟩
  append_controls [hAux, hState, hOwner, hPointer, hLayer, hTracker, hNew, hSeparate,
    Ne.symm hSeparate, hSub, func29Def]
  apply hNext
  simp [hAux]

#print axioms append_tail_release_spec
end Project.Drone.Execution
