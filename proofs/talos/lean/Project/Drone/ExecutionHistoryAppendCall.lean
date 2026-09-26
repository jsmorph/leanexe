import Project.Drone.ExecutionHistoryAppendPrepare

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
theorem history_append_call_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel index : Nat) (terrain previous history out0 out1 layer : UInt64)
    (aux : List Value) (s : Scratch) (hAux : aux.length = 44) (hIndex : index + 1 < UInt64.size)
    (hLayer0 : aux[21]? = some (.i64 layer)) (hLayer1 : aux[22]? = some (.i64 layer))
    (P : Store Unit → UInt64 → Prop)
    (hCall : TerminatesWith env Project.Drone.«module» 21 store
      [.i64 history, .i64 history, .i64 layer, .i64 layer, .i64 0, .i64 45]
      (fun final values => ∃ root : UInt64, values = [.i64 root, .i64 root] ∧ P final root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (root : UInt64) (nextAux : List Value) (nextScratch : Scratch),
      nextAux.length = 44 → nextAux[23]? = some (.i64 (UInt64.ofNat (index + 1))) →
      nextAux[24]? = some (.i64 0) → nextAux[25]? = some (.i64 terrain) →
      nextAux[26]? = some (.i64 layer) → nextAux[27]? = some (.i64 layer) →
      nextAux[37]? = some (.i64 root) → nextAux[38]? = some (.i64 root) →
      P final root → wp Project.Drone.«module» rest Q final
        (historyFrame fuel index terrain previous history out0 out1 nextAux nextScratch) env) :
    wp Project.Drone.«module» ((historyLoopBody.drop 130).take 47 ++ rest) Q store
      (historyFrame fuel index terrain previous history out0 out1 aux s) env := by
  have hCode : (historyLoopBody.drop 130).take 47 = (historyLoopBody.drop 130).take 34 ++
      (historyLoopBody.drop 164).take 13 := rfl
  rw [hCode, List.append_assoc]
  apply history_append_prepare_spec env store fuel index terrain previous history out0 out1 layer aux s
    hAux hIndex hLayer0 hLayer1
  simp only [historyLoopBody, func22, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.take, List.cons_append, List.nil_append]
  wp_history_frame [hAux, historyAppendAux, historyAppendScratch]
  refine wp_call_tw hCall ?_
  rintro final values ⟨root, rfl, hP⟩
  wp_history_frame [hAux, func21Def]
  refine hNext final root _ (historyAppendScratch s index) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hP <;>
    simp [hAux, historyAppendAux]

#print axioms history_append_call_spec
end Project.Drone.Execution
