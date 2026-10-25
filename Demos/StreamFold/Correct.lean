import Demos.StreamFold.Future

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

variable {Acc : Type} {kernel : Kernel Acc} (spec : KernelSpec kernel) {seed : Acc}

theorem process_exec_correct {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {state : (BufferState Acc)} {world final : World} {trace : List Event} {outcome : Outcome UInt64}
    (execution : Process.Exec host (process kernel seed) state world trace outcome final)
    {position : StreamPosition} {history expected : List Bytes}
    (represented : rep position world) (future : StreamFuture spec state position history expected) :
    ∃ nextPosition, rep nextPosition final ∧ outcome = .returned 0 ∧
      nextPosition.input = [] ∧ nextPosition.output = outputWords expected := by
  induction execution generalizing position history with
  | done execution stopped =>
      obtain ⟨nextPosition, nextRep, _, finished⟩ :=
        streamFuture_step spec streams represented future execution
      obtain ⟨status, input, output⟩ := finished stopped
      exact ⟨nextPosition, nextRep, congrArg Outcome.returned status, input, output⟩
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
    {history expected : List Bytes} (represented : rep position world)
    (future : StreamFuture spec state position history expected) :
    ∃ trace final nextPosition,
      Process.Exec host (process kernel seed) state world trace (.returned 0) final ∧
      rep nextPosition final ∧ nextPosition.input = [] ∧
      nextPosition.output = outputWords expected := by
  obtain ⟨trace, status, final, _, execution, _, _⟩ :=
    process_terminates spec streams.progress represented future.safe
  obtain ⟨nextPosition, nextRep, returned, input, output⟩ :=
    process_exec_correct spec streams execution represented future
  cases returned
  exact ⟨trace, final, nextPosition, execution, nextRep, input, output⟩

theorem initial_terminates_output {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    (seed : Acc) {position : StreamPosition} {world : World}
    (represented : rep position world) (empty : position.output = [])
    (good : spec.Good seed) (expected : List Bytes)
    (modelSafe : Model.Safe spec (Model.initial seed) position.input)
    (finalRoom : ∀ final, Model.consume kernel (Model.initial seed) position.input = .ok final →
      final.pending.size ≠ 0 → spec.Room final.total final.pending)
    (completion : ∃ processed final,
      Model.consume kernel (Model.initial seed) position.input = .ok processed ∧
      Model.finish kernel processed = .ok final ∧ final.output = expected) :
    ∃ trace final nextPosition,
      Process.Exec host (process kernel seed) (initial seed) world trace (.returned 0) final ∧
      rep nextPosition final ∧ nextPosition.input = [] ∧
      nextPosition.output = outputWords expected :=
  process_terminates_future spec streams represented
    (streamFuture_initial spec seed position empty good expected modelSafe finalRoom completion)

end Demos.StreamFold
