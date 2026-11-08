import Demos.OrderBook.ProcessCompiledCorrect

/-! The axiom audit of the order book's process, native and compiled: every theorem in the
namespace `Demos.OrderBook.Process`, which holds the native proofs, the declarations that
`verified_compile_wasi` generates under `io`, the module's theorems, and the charges, every theorem
of the closed forms of `run`'s bound in `Demos.OrderBook.Bound`, the lemmas about `Spec.run` that
the process's batch lemma adds, and the lemmas about `Program` that bound the events of a record
and keep the sizes of the book's arrays use only `propext`, `Classical.choice`, and `Quot.sound`.
The full check's build reports the `#print axioms` lines and fails on the audit's error. -/

open Lean Elab Command in
run_cmd do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let added := [``Demos.OrderBook.Spec.foldl_nextId_le, ``Demos.OrderBook.Spec.run_nextId_le,
    ``Demos.OrderBook.Spec.foldl_events_length, ``Demos.OrderBook.Spec.run_events_length,
    ``Demos.OrderBook.Spec.encodeAll_size,
    ``Demos.OrderBook.Program.matchStep_out_size,
    ``Demos.OrderBook.Program.repeatWhile_out_size, ``Demos.OrderBook.Program.fillArrays_out_size,
    ``Demos.OrderBook.Program.submitArrays_out_size, ``Demos.OrderBook.Program.step_out_size,
    ``Demos.OrderBook.Program.fold_out_size, ``Demos.OrderBook.Program.loop_out_size,
    ``Demos.OrderBook.Program.run_out_size, ``Demos.OrderBook.Program.unlink_sizes,
    ``Demos.OrderBook.Program.place_sizes, ``Demos.OrderBook.Program.matchStep_sizes,
    ``Demos.OrderBook.Program.repeatWhile_sizes, ``Demos.OrderBook.Program.fillArrays_sizes,
    ``Demos.OrderBook.Program.submitArrays_sizes, ``Demos.OrderBook.Program.step_sizes]
  let env ← getEnv
  let theorems := env.constants.toList.filterMap fun (name, info) =>
    if ((`Demos.OrderBook.Process).isPrefixOf name || (`Demos.OrderBook.Bound).isPrefixOf name) &&
        info matches .thmInfo _ then some name
    else none
  for declaration in theorems ++ added do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"Order book process axiom check passed for {theorems.length + added.length} theorems"

#print axioms Demos.OrderBook.Process.process_output
#print axioms Demos.OrderBook.Process.process_exec_correct
#print axioms Demos.OrderBook.Process.process_terminates
#print axioms Demos.OrderBook.Process.process_terminates_future
#print axioms Demos.OrderBook.Process.batch_refines
#print axioms Demos.OrderBook.Process.future_step
#print axioms Demos.OrderBook.Process.initial_terminates
#print axioms Demos.OrderBook.Process.terminates_bytes
#print axioms Demos.OrderBook.Process.runBound_74
#print axioms Demos.OrderBook.Bound.run_bound_le_sized
#print axioms Demos.OrderBook.Process.terminates_of_room
#print axioms Demos.OrderBook.Process.implements
#print axioms Demos.OrderBook.Process.run_initial
#print axioms Demos.OrderBook.Process.bytes
#print axioms Demos.OrderBook.Process.target_terminates
#print axioms Demos.OrderBook.Process.step_prefix_bound
