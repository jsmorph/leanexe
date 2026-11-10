import Demos.Rcv.ProcessFuture

/-! The correctness of [the tabulator's process](Process.lean) under StreamFold's host
assumptions.  `process_output` states that, from the initial state and an empty output history,
some execution reads the whole input, writes exactly the bytes of the report of the input, the
requirements' `report b` for the bytes `b` of the input, and returns status 0.  Its premises are the
host assumptions `StreamHost` and an input of fewer than `2 ^ 32` bytes, the most that a buffer of
the module holds.  `process_exec_correct` states that every finite execution from a state with the
invariant returns status 0 after writing that report, and `process_terminates` of
[the control](ProcessControl.lean) gives an execution that returns. -/

namespace Demos.Rcv.Process

open LeanExe LeanExe.Wasi
open Demos.StreamFold (StreamPosition StreamHost)

/-- Every finite execution from a state with the invariant returns status 0, after writing exactly
the bytes of `expectedOutput`, with the whole input read. -/
theorem process_exec_correct {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {input : List UInt64} (short : input.length < 2 ^ 32)
    {s : State} {world final : World} {trace : List Event} {outcome : Outcome UInt64}
    (execution : Process.Exec host process s world trace outcome final)
    {position : StreamPosition} (represented : rep position world)
    (future : Future input s position) :
    ∃ next, rep next final ∧ outcome = .returned 0 ∧
      next.output = expectedOutput input ∧ next.input = [] := by
  induction execution generalizing position with
  | done execution stopped =>
      obtain ⟨next, nextRep, _, finished⟩ := future_step streams short represented future execution
      obtain ⟨status, output, noInput⟩ := finished stopped
      exact ⟨next, nextRep, congrArg Outcome.returned status, output, noInput⟩
  | next execution running continuation ih =>
      obtain ⟨next, nextRep, continued, _⟩ := future_step streams short represented future execution
      exact ih nextRep (continued running)
  | exit execution =>
      obtain ⟨next, impossible⟩ :=
        step_returned streams.progress represented future.safe execution
      cases impossible
  | trap execution =>
      obtain ⟨next, impossible⟩ :=
        step_returned streams.progress represented future.safe execution
      cases impossible

/-- From a state with the invariant, some execution returns status 0 after writing exactly the
bytes of `expectedOutput`, with the whole input read. -/
theorem process_terminates_future {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {input : List UInt64} (short : input.length < 2 ^ 32)
    {s : State} {position : StreamPosition} {world : World}
    (represented : rep position world) (future : Future input s position) :
    ∃ trace final next,
      Process.Exec host process s world trace (.returned 0) final ∧
      rep next final ∧ next.output = expectedOutput input ∧ next.input = [] := by
  obtain ⟨trace, final, _, execution, _⟩ :=
    process_terminates streams.progress represented future.safe
  obtain ⟨next, nextRep, _, output, noInput⟩ :=
    process_exec_correct streams short execution represented future
  exact ⟨trace, final, next, execution, nextRep, output, noInput⟩

/-- From the initial state and an empty output history, some execution reads the whole input,
writes exactly the bytes of the report of the input, and returns status 0. -/
theorem process_output {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world : World} (represented : rep position world)
    (empty : position.output = []) (short : position.input.length < 2 ^ 32) :
    ∃ trace final next,
      Process.Exec host process initial world trace (.returned 0) final ∧
      rep next final ∧ next.output = expectedOutput position.input ∧ next.input = [] :=
  process_terminates_future streams short represented (future_initial position empty)

end Demos.Rcv.Process
