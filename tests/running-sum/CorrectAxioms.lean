import Demos.RunningSum.Correct

open Lean Elab Command in
elab "check_running_sum_correctness_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``LeanExe.Wasi.Process.exec_of_wellFounded,
    ``Wasm.wp.with_execution,
    ``Wasm.wp_loop_ghost,
    ``Verified.Wasi.wp_process_iteration_total,
    ``Verified.Wasi.wp_process_entry_total,
    ``Verified.Wasi.compiled_process_total_body,
    ``Verified.Wasi.compiled_process_total_run,
    ``Demos.RunningSum.Termination.consumeInput_cursor,
    ``Demos.RunningSum.Termination.rank_wellFounded,
    ``Demos.RunningSum.Termination.step_returned,
    ``Demos.RunningSum.Termination.initial_terminates,
    ``Demos.RunningSum.Termination.target_terminates,
    ``Demos.RunningSum.remainingOutput_words,
    ``Demos.RunningSum.afterWrite_conservation,
    ``Demos.RunningSum.consumeInput_buffer,
    ``Demos.RunningSum.StreamHost.progress,
    ``Demos.RunningSum.streamFuture_initial,
    ``Demos.RunningSum.streamFuture_step,
    ``Demos.RunningSum.StreamHost.observed,
    ``Demos.RunningSum.observedStreamRep_exit_output,
    ``Demos.RunningSum.observedStreamRep_exitTrap_output,
    ``Demos.RunningSum.outputWords_correct,
    ``Demos.RunningSum.process_exec_integer,
    ``Demos.RunningSum.process_terminates_integer,
    ``Demos.RunningSum.command_integer,
    ``Demos.RunningSum.result_integer,
    ``Demos.RunningSum.terminates_integer,
    ``Demos.RunningSum.initial_terminates_integer,
    ``Demos.RunningSum.integer_bytes]
  for declaration in declarations do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"Running sum correctness axiom check passed for {declarations.size} theorems"

check_running_sum_correctness_axioms
