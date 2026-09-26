import Project.Drone.ExecutionHistoryFrame
import Project.Drone.ExecutionRead
import Project.ProofKit.NatSub
import Project.ProofKit.CheckedNatAdd

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
set_option maxHeartbeats 250000 in
theorem history_read_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel index : Nat) (terrain previous history out0 out1 : UInt64) (aux : List Value) (s : Scratch)
    (heights : Array UInt64) (hAux : aux.length = 44) (hTerrain : UInt64Array.At store terrain heights)
    (hIndex : index < heights.size) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (nextAux : List Value) (nextScratch : Scratch), nextAux.length = 44 →
      nextAux[1]? = some (.i64 45) → nextAux[2]? = some (.i64 0) →
      nextAux[7]? = some (.i64 (floorAt heights (index - 1))) →
      nextAux[12]? = some (.i64 (floorAt heights index)) →
      nextAux[13]? = some (.i64 (if index + 1 == heights.size then 1 else 0)) →
      nextAux[14]? = some (.i64 previous) → nextAux[15]? = some (.i64 previous) →
      wp Project.Drone.«module» rest Q store
        (historyFrame fuel index terrain previous history out0 out1 nextAux nextScratch) env) :
    wp Project.Drone.«module» ((historyLoopBody.drop 7).take 62 ++ rest) Q store
      (historyFrame fuel index terrain previous history out0 out1 aux s) env := by
  have hSize := hTerrain.size_lt
  have hIndex64 : index < UInt64.size := by omega
  have hNext64 : index + 1 < UInt64.size := by omega
  have hGuard := CheckedNatAdd.guard_of_fits index 1 hNext64
  have hLast : UInt64.ofNat index + 1 = UInt64.ofNat heights.size ↔ index + 1 = heights.size := by
    change UInt64.ofNat index + UInt64.ofNat 1 = UInt64.ofNat heights.size ↔ _
    rw [← UInt64.ofNat_add, eq_comm, hTerrain.encodedSize_eq hNext64, eq_comm]
  have hRead : store.mem.read64 (UInt32.ofNat (terrain.toNat % 4294967296)) = UInt64.ofNat heights.size := by
    rw [hTerrain.pointerAddress_eq]
    exact hTerrain.lengthRead
  simp only [historyLoopBody, func22, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.take, List.cons_append, List.nil_append]
  refine wp_call_tw (stateCount_exact env store) ?_
  rintro finish values ⟨rfl, rfl⟩
  wp_history_frame [hAux, func16Def, stateCount, show UInt64.ofNat 45 = 45 from rfl]
  refine NatSub.guard_spec 63 64 _ _ _ _ index 1 [] rfl ?_ ?_ hIndex64 (by decide) _ _ ?_
  · simp [Locals.get, hAux]
  · simp [Locals.get, hAux]
  wp_history_frame [hAux]
  refine wp_call_tw (floorAt_exact env _ terrain terrain heights (index - 1) hTerrain (by omega)) ?_
  rintro finish values ⟨rfl, rfl⟩
  wp_history_frame [hAux, func20Def]
  refine wp_call_tw (floorAt_exact env _ terrain terrain heights index hTerrain hIndex) ?_
  rintro finish values ⟨rfl, rfl⟩
  wp_history_frame [hAux, func20Def]
  refine CheckedNatAdd.guard_spec 65 _ _ _ _ index 1 [] rfl ?_ hNext64 _ _ ?_
  · simp [Locals.get, hAux, UInt64.ofNat_add]
  by_cases hEnd : index + 1 = heights.size
  all_goals
    have hLengthBound := hTerrain.generatedLengthBound
    history_controls [hAux, hRead, hLengthBound, hTerrain.pointerAddress_eq,
      UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl, hLast, hEnd]
    simp only [Nat.reducePow, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero,
      hRead, hLengthBound, hTerrain.pointerAddress_eq, hTerrain.lengthRead,
      not_lt_of_ge hTerrain.lengthBound, ↓reduceIte]
    history_controls [hAux, hLast, hEnd]
    refine hNext _ { s with counter := terrain, value := 1, spare0 := UInt64.ofNat index + 1 }
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [hAux, hEnd]

#print axioms history_read_spec
end Project.Drone.Execution
