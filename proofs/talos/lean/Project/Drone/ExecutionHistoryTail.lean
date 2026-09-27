import Project.Drone.ExecutionHistoryFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxRecDepth 32768 in
set_option maxHeartbeats 300000 in
theorem history_tail_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel index : Nat) (terrain previous history out0 out1 layer root : UInt64)
    (aux : List Value) (s : Scratch) (hAux : aux.length = 44)
    (hIndex : aux[23]? = some (.i64 (UInt64.ofNat (index + 1))))
    (hTerrain0 : aux[24]? = some (.i64 0)) (hTerrain1 : aux[25]? = some (.i64 terrain))
    (hLayer0 : aux[26]? = some (.i64 layer)) (hLayer1 : aux[27]? = some (.i64 layer))
    (hRoot0 : aux[37]? = some (.i64 root)) (hRoot1 : aux[38]? = some (.i64 root))
    (hTerrain : terrain ≠ 0) (hLayer : layer ≠ 0) (hRoot : root ≠ 0)
    (Q : Assertion Unit)
    (hNext : ∀ (nextAux : List Value) (nextScratch : Scratch), nextAux.length = 44 →
      Q (.Break 0 store (historyFrame fuel (index + 1) terrain layer root out0 out1 nextAux nextScratch))) :
    wp Project.Drone.«module» (historyLoopBody.drop 177) Q store
      (historyFrame (fuel + 1) index terrain previous history out0 out1 aux s) env := by
  have hSub : UInt64.ofNat (fuel + 1) - 1 = UInt64.ofNat fuel := by
    rw [UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl, UInt64.add_sub_cancel]
  simp only [historyLoopBody, func22, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop]
  history_controls [hAux, hIndex, hTerrain0, hTerrain1, hLayer0, hLayer1, hRoot0, hRoot1,
    hTerrain, hLayer, hRoot, hSub]
  apply hNext _ { s with source := root, length := root, count := 0, nextLength := 0, target := 0 }
  simp [hAux]

#print axioms history_tail_spec
end Project.Drone.Execution
