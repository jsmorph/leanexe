import Demos.StreamFold.Correct
import Demos.StreamFold.Map

open Lean Elab Command in
elab "check_stream_fold_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Demos.StreamFold.repeatWhile_map,
    ``Demos.StreamFold.consumeInput_safe,
    ``Demos.StreamFold.consumeInput_cursor,
    ``Demos.StreamFold.afterRead_safe,
    ``Demos.StreamFold.afterWrite_safe,
    ``Demos.StreamFold.remainingOutput_words,
    ``Demos.StreamFold.afterWrite_conservation,
    ``Demos.StreamFold.consumeInput_buffer,
    ``Demos.StreamFold.rank_wellFounded,
    ``Demos.StreamFold.step_returned,
    ``Demos.StreamFold.step_advances,
    ``Demos.StreamFold.process_terminates,
    ``Demos.StreamFold.initial_terminates,
    ``Demos.StreamFold.Model.consume_append,
    ``Demos.StreamFold.Model.safe_append_iff,
    ``Demos.StreamFold.Model.consume_lines,
    ``Demos.StreamFold.Model.foldLines_append,
    ``Demos.StreamFold.Model.finish_consume_input,
    ``Demos.StreamFold.Model.safe_of_lines,
    ``Demos.StreamFold.Model.LineRooms.after_fold,
    ``Demos.StreamFold.Model.validInput_safe_and_finalRoom,
    ``Demos.StreamFold.streamFuture_initial,
    ``Demos.StreamFold.streamFuture_step,
    ``Demos.StreamFold.process_exec_correct,
    ``Demos.StreamFold.process_terminates_future,
    ``Demos.StreamFold.initial_terminates_output]
  for declaration in declarations do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"Stream fold axiom check passed for {declarations.size} theorems"

check_stream_fold_axioms
