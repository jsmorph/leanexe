import Project.Drone.ExecutionEmptyBudget
import Project.Drone.ExecutionInitialInvariant

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush LeanExe.Examples.Drone

set_option maxRecDepth 32768 in
theorem initial_start_spec (env : HostEnv Unit) (store : Store Unit)
    (seed previous current capacity next : UInt64) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (aux : List Value) (s : Scratch), aux.length = 21 →
      wp Project.Drone.«module» rest Q store (initialFrame seed seed 0 false aux s 0 0) env) :
    wp Project.Drone.«module» ((func23.drop 40).take 17 ++ rest) Q store
      { WordArrayPush.frame [] (List.replicate 22 (.i64 0)) (List.replicate 12 (.i64 0))
          (emptyScratch zeroPushScratch seed previous current capacity next) with values := [.i64 seed] } env := by
  simp only [func23, List.drop, List.take, List.cons_append, List.nil_append]
  wp_fixed_frame [WordArrayPush.frame, emptyScratch, allocatedScratch, zeroPushScratch,
    Scratch.words, List.replicate, List.cons_append, List.nil_append]
  refine wp_call_tw (stateCount_exact env store) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_fixed_frame [func16Def, stateCount, show UInt64.ofNat 45 = 45 from rfl]
  exact hNext (List.replicate 21 (.i64 0))
    ⟨0, 8, previous, current, capacity, next, seed, 0, 0, 0, 0, 0, 0, 0, 0⟩ rfl

set_option maxRecDepth 32768 in
theorem initial_entry (env : HostEnv Unit) (store : Store Unit) (P : Store Unit → List Value → Prop)
    (hNext : wp Project.Drone.«module» (emptyProgram 22 ++ func23.drop 40)
      (fun c => match c with
        | .Fallthrough final frame => P final (frame.values.take 2)
        | .Return final values => P final (values.take 2)
        | _ => False)
      store (WordArrayPush.frame [] (List.replicate 22 (.i64 0))
        (List.replicate 12 (.i64 0)) zeroPushScratch) env) :
    TerminatesWith env Project.Drone.«module» 23 store [] P := by
  refine TerminatesWith.of_wp_entry_for (f := func23Def) rfl ?_
  change wp Project.Drone.«module» func23 _ store { params := [], locals := List.replicate 49 (.i64 0) } env
  have hProgram : func23 = emptyProgram 22 ++ func23.drop 40 := rfl
  rw [hProgram]
  convert hNext using 1
  · funext c
    cases c <;> simp [func23Def, Function.numParams]
  · rfl

#print axioms initial_start_spec
#print axioms initial_entry
end Project.Drone.Execution
