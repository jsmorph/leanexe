import Demos.RunningSumFp.Correct

open Lean Elab Command in
elab "check_running_sumfp_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Demos.RunningSumFp.io.step.related,
    ``Demos.RunningSumFp.io.step.implements,
    ``Demos.RunningSumFp.io.stackFits,
    ``Demos.RunningSumFp.command.validity,
    ``Demos.RunningSumFp.command.validBinary,
    ``Demos.RunningSumFp.command.bytes,
    ``Demos.RunningSumFp.stackFits,
    ``Demos.RunningSumFp.calls,
    ``Demos.RunningSumFp.step_related,
    ``Demos.RunningSumFp.begin_related,
    ``Demos.RunningSumFp.initialState,
    ``Demos.RunningSumFp.implements,
    ``Demos.RunningSumFp.run_initial,
    ``Demos.RunningSumFp.bytes,
    ``Demos.RunningSumFp.parse_accept,
    ``Demos.RunningSumFp.parse_reject,
    ``Demos.RunningSumFp.parse_bits,
    ``Demos.RunningSumFp.add_bits,
    ``Demos.RunningSumFp.prefixFloats_bits,
    ``Demos.RunningSumFp.render_text,
    ``Demos.RunningSumFp.render_roundtrip,
    ``Demos.RunningSumFp.render_shortest,
    ``Demos.RunningSumFp.render_nonempty,
    ``Demos.RunningSumFp.render_size_bound,
    ``Demos.RunningSumFp.words_injective,
    ``Demos.RunningSumFp.inputLine_unique,
    ``Demos.RunningSumFp.lineRooms,
    ``Demos.RunningSumFp.foldOutcome_fp,
    ``Demos.RunningSumFp.inputValues_exist,
    ``Demos.RunningSumFp.inputValues_unique,
    ``Demos.RunningSumFp.foldOutcome_input,
    ``Demos.RunningSumFp.process_fp_correct,
    ``Demos.RunningSumFp.process_terminates_fp,
    ``Demos.RunningSumFp.command_fp,
    ``Demos.RunningSumFp.Termination.step_returned,
    ``Demos.RunningSumFp.Termination.step_advances,
    ``Demos.RunningSumFp.Termination.control_wellFounded,
    ``Demos.RunningSumFp.Termination.control_step_replies,
    ``Demos.RunningSumFp.Termination.target_terminates,
    ``Demos.RunningSumFp.result_fp,
    ``Demos.RunningSumFp.terminates_fp,
    ``Demos.RunningSumFp.initial_terminates_fp,
    ``Demos.RunningSumFp.fp_bytes]
  for declaration in declarations do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"Running sumfp axiom check passed for {declarations.size} theorems"

check_running_sumfp_axioms
