import Demos.StreamFold.Future

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

variable {Acc : Type} {kernel : Kernel Acc} (spec : KernelSpec kernel) {seed : Acc}

theorem process_exec_correct {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {state : BufferState Acc} {world final : World} {trace : List Event} {outcome : Outcome UInt64}
    (execution : Process.Exec host (process kernel seed) state world trace outcome final)
    {position : StreamPosition} {history expected : List Bytes} {status : UInt64}
    (represented : rep position world)
    (future : StreamFuture spec state position history expected status) :
    ∃ nextPosition, rep nextPosition final ∧ outcome = .returned status ∧
      StreamDone nextPosition expected status := by
  induction execution generalizing position history with
  | done execution stopped =>
      obtain ⟨nextPosition, nextRep, _, finished⟩ :=
        streamFuture_step spec streams represented future execution
      obtain ⟨statusEq, done⟩ := finished stopped
      exact ⟨nextPosition, nextRep, congrArg Outcome.returned statusEq, done⟩
  | next execution running continuation ih =>
      obtain ⟨nextPosition, nextRep, continued, _⟩ :=
        streamFuture_step spec streams represented future execution
      obtain ⟨nextHistory, nextFuture⟩ := continued running
      exact ih nextRep nextFuture
  | exit execution =>
      obtain ⟨next, impossible⟩ :=
        step_returned streams.progress represented future.safe execution
      cases impossible
  | trap execution =>
      obtain ⟨next, impossible⟩ :=
        step_returned streams.progress represented future.safe execution
      cases impossible

theorem process_terminates_future {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {state : BufferState Acc} {position : StreamPosition} {world : World}
    {history expected : List Bytes} {status : UInt64} (represented : rep position world)
    (future : StreamFuture spec state position history expected status) :
    ∃ trace final nextPosition,
      Process.Exec host (process kernel seed) state world trace (.returned status) final ∧
      rep nextPosition final ∧ StreamDone nextPosition expected status := by
  obtain ⟨trace, returned, final, _, execution, _, _⟩ :=
    process_terminates spec streams.progress represented future.safe
  obtain ⟨nextPosition, nextRep, same, done⟩ :=
    process_exec_correct spec streams execution represented future
  cases same
  exact ⟨trace, final, nextPosition, execution, nextRep, done⟩

/-- From the initial state, the process returns the status of the kernel's fold over the lines of
the input, after writing the outputs of the lines before the first rejected line. -/
theorem initial_terminates_output {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    (seed : Acc) {position : StreamPosition} {world : World}
    (represented : rep position world) (empty : position.output = [])
    (good : spec.Good seed) (rooms : Model.LineRooms spec seed (Model.lines position.input)) :
    ∃ trace final nextPosition,
      Process.Exec host (process kernel seed) (initial seed) world trace
        (.returned (Model.foldOutcome kernel seed (Model.lines position.input)).2) final ∧
      rep nextPosition final ∧
      StreamDone nextPosition (Model.foldOutcome kernel seed (Model.lines position.input)).1
        (Model.foldOutcome kernel seed (Model.lines position.input)).2 :=
  process_terminates_future spec streams represented
    (streamFuture_initial spec seed position empty good rooms)

end Demos.StreamFold
