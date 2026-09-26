import Project.Drone.ExecutionAdvanceInvariant

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush LeanExe.Examples.Drone

def advanceEntryParams (r0 r1 : UInt64) (last : Bool) (previous : UInt64) : List Value :=
  [.i64 r0, .i64 r1, .i64 (if last then 1 else 0), .i64 previous, .i64 previous]

def advanceEntrySaved (r0 r1 : UInt64) (last : Bool) (previous : UInt64) : List Value :=
  [.i64 45, .i64 45, .i64 0, .i64 r0, .i64 r1,
    .i64 (if last then 1 else 0), .i64 previous, .i64 previous, .i64 0, .i64 0]

set_option maxRecDepth 32768 in
theorem advance_prefix_spec (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 : UInt64) (last : Bool) (previous : UInt64) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.Drone.«module» rest Q initial
      (WordArrayPush.frame (advanceEntryParams r0 r1 last previous)
        (advanceEntrySaved r0 r1 last previous) [] zeroPushScratch) env) :
    wp Project.Drone.«module» (func19.take 16 ++ rest) Q initial
      { params := advanceEntryParams r0 r1 last previous, locals := List.replicate 25 (.i64 0) } env := by
  simp only [func19, List.take, List.cons_append, List.nil_append]
  refine wp_call_tw (stateCount_exact env initial) ?_
  rintro finish values ⟨hFinish, rfl⟩
  subst finish
  wp_fixed_frame [func16Def, stateCount, advanceEntryParams]
  simpa only [WordArrayPush.frame, Scratch.words, advanceEntryParams, advanceEntrySaved,
    zeroPushScratch, List.cons_append, List.nil_append, show UInt64.ofNat 45 = 45 from rfl] using hNext

set_option maxRecDepth 32768 in
theorem advance_entry (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 : UInt64) (last : Bool) (previous : UInt64) (P : Store Unit → List Value → Prop)
    (hNext : wp Project.Drone.«module» (func19.drop 16)
      (fun c => match c with
        | .Fallthrough store frame => P store (frame.values.take 2)
        | .Return store values => P store (values.take 2)
        | _ => False)
      initial (WordArrayPush.frame (advanceEntryParams r0 r1 last previous)
        (advanceEntrySaved r0 r1 last previous) [] zeroPushScratch) env) :
    TerminatesWith env Project.Drone.«module» 19 initial
      [.i64 previous, .i64 previous, .i64 (if last then 1 else 0), .i64 r1, .i64 r0] P := by
  refine TerminatesWith.of_wp_entry_for (f := func19Def) rfl ?_
  change wp Project.Drone.«module» func19 _ initial
    { params := advanceEntryParams r0 r1 last previous, locals := List.replicate 25 (.i64 0) } env
  rw [← List.take_append_drop 16 func19]
  apply advance_prefix_spec
  convert hNext using 1
  funext c
  cases c <;> simp [func19Def, Function.numParams]

#print axioms advance_prefix_spec
#print axioms advance_entry
end Project.Drone.Execution
