import Project.Drone.ExecutionHistoryFrame
import Project.ProofKit.CheckedNatAdd

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush LeanExe.Examples.Drone

def historyAppendAux (aux : List Value) (index : Nat) (terrain layer history : UInt64) : List Value :=
  (((((((((((aux.set 23 (.i64 (UInt64.ofNat (index + 1)))).set 24 (.i64 terrain)).set 25 (.i64 terrain)).set
    26 (.i64 layer)).set 27 (.i64 layer)).set 28 (.i64 45)).set 29 (.i64 45)).set 30 (.i64 0)).set
    31 (.i64 layer)).set 32 (.i64 layer)).set 33 (.i64 history)).set 34 (.i64 history)

def historyAppendScratch (s : Scratch) (index : Nat) : Scratch :=
  { s with counter := UInt64.ofNat index, value := 1, spare0 := UInt64.ofNat (index + 1) }

set_option maxRecDepth 32768 in
theorem history_append_prepare_spec (env : HostEnv Unit) (store : Store Unit)
    (fuel index : Nat) (terrain previous history out0 out1 layer : UInt64)
    (aux : List Value) (s : Scratch) (hAux : aux.length = 44) (hIndex : index + 1 < UInt64.size)
    (hLayer0 : aux[21]? = some (.i64 layer)) (hLayer1 : aux[22]? = some (.i64 layer))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.Drone.«module» rest Q store
      (historyFrame fuel index terrain previous history out0 out1
        (historyAppendAux aux index terrain layer history) (historyAppendScratch s index)) env) :
    wp Project.Drone.«module» ((historyLoopBody.drop 130).take 34 ++ rest) Q store
      (historyFrame fuel index terrain previous history out0 out1 aux s) env := by
  simp only [historyLoopBody, func22, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.take, List.cons_append, List.nil_append]
  wp_history_frame [hAux]
  refine CheckedNatAdd.guard_spec 65 _ _ _ _ index 1 [] rfl ?_ hIndex _ _ ?_
  · simp [Locals.get, hAux, UInt64.ofNat_add]
  wp_history_frame [hAux, hLayer0, hLayer1]
  refine wp_call_tw (stateCount_exact env store) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_history_frame [hAux, hLayer0, hLayer1, func16Def, stateCount, show UInt64.ofNat 45 = 45 from rfl]
  simpa only [historyFrame, historyParams, historyAppendAux, historyAppendScratch, Scratch.words,
    List.cons_append, List.nil_append, UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl] using hNext

#print axioms history_append_prepare_spec
end Project.Drone.Execution
