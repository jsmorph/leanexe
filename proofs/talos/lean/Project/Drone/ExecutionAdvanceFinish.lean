import Project.Drone.ExecutionAdvanceEntry
import Project.Drone.ExecutionEmptyProgram

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxRecDepth 32768 in
theorem advance_finish_spec (env : HostEnv Unit) (store : Store Unit)
    (r0 r1 : UInt64) (last : Bool) (previous root scratchPrevious current capacity next : UInt64)
    (P : Store Unit → List Value → Prop)
    (hCall : TerminatesWith env Project.Drone.«module» 18 store
      [.i64 root, .i64 root, .i64 previous, .i64 previous, .i64 (if last then 1 else 0),
        .i64 r1, .i64 r0, .i64 0, .i64 45]
      (fun final values => ∃ output : UInt64, values = [.i64 output, .i64 output] ∧ P final values)) :
    wp Project.Drone.«module» (func19.drop 56)
      (fun c => match c with
        | .Fallthrough final frame => P final (frame.values.take 2)
        | .Return final values => P final (values.take 2)
        | _ => False)
      store { WordArrayPush.frame (advanceEntryParams r0 r1 last previous)
        (advanceEntrySaved r0 r1 last previous) []
        (emptyScratch zeroPushScratch root scratchPrevious current capacity next) with values := [.i64 root] } env := by
  simp only [func19, List.drop]
  wp_fixed_frame [WordArrayPush.frame, Scratch.words, advanceEntryParams, advanceEntrySaved,
    zeroPushScratch, emptyScratch, allocatedScratch]
  refine wp_call_tw hCall ?_
  rintro final values ⟨output, rfl, hP⟩
  wp_fixed_frame [func18Def, func19Def]
  exact hP

#print axioms advance_finish_spec
end Project.Drone.Execution
