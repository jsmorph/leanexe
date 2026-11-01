import Demos.OrderBook.ProcessFuture

/-! The correctness of [the order book's process](Process.lean) under StreamFold's host
assumptions.  `process_output` states that, from the initial state and an empty output history,
some execution reads the whole input, writes exactly the little-endian bytes of the event words of
`Spec.run` from the empty book on the whole words of the input, and returns status 0 when the input
fills whole words and 28 otherwise.  Its premises are the host assumptions `StreamHost` and the
requirements' bound of fewer than 2^64 - 1 records.  `process_exec_correct` states that every
finite execution from a state with the invariant returns that status after writing those bytes,
and `process_terminates` of [the control](ProcessControl.lean) gives an execution that returns. -/

namespace Demos.OrderBook.Process

open LeanExe LeanExe.Wasi
open Demos.StreamFold (StreamPosition StreamHost)

/-- Every finite execution from a state with the invariant returns `expectedStatus` of the input,
after writing exactly the bytes of `expectedOutput`, with the whole input read. -/
theorem process_exec_correct {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {input : List UInt64} (ids : (Spec.records (leWords input)).length < 2 ^ 64 - 1)
    {s : State} {world final : World} {trace : List Event} {outcome : Outcome UInt64}
    (execution : Process.Exec host process s world trace outcome final)
    {position : StreamPosition} {processed : List UInt64}
    (represented : rep position world) (future : Future input s position processed) :
    ∃ next, rep next final ∧ outcome = .returned (expectedStatus input) ∧
      next.output = expectedOutput input ∧ next.input = [] := by
  induction execution generalizing position processed with
  | done execution stopped =>
      obtain ⟨next, nextRep, _, finished⟩ := future_step streams ids represented future execution
      obtain ⟨status, output, noInput⟩ := finished stopped
      exact ⟨next, nextRep, congrArg Outcome.returned status, output, noInput⟩
  | next execution running continuation ih =>
      obtain ⟨next, nextRep, continued, _⟩ := future_step streams ids represented future execution
      obtain ⟨processed', nextFuture⟩ := continued running
      exact ih nextRep nextFuture
  | exit execution =>
      obtain ⟨next, impossible⟩ :=
        step_returned streams.progress represented future.safe execution
      cases impossible
  | trap execution =>
      obtain ⟨next, impossible⟩ :=
        step_returned streams.progress represented future.safe execution
      cases impossible

/-- From a state with the invariant, some execution returns `expectedStatus` of the input after
writing exactly the bytes of `expectedOutput`, with the whole input read. -/
theorem process_terminates_future {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {input : List UInt64} (ids : (Spec.records (leWords input)).length < 2 ^ 64 - 1)
    {s : State} {position : StreamPosition} {processed : List UInt64} {world : World}
    (represented : rep position world) (future : Future input s position processed) :
    ∃ trace final next,
      Process.Exec host process s world trace (.returned (expectedStatus input)) final ∧
      rep next final ∧ next.output = expectedOutput input ∧ next.input = [] := by
  obtain ⟨trace, returned, final, _, execution, _, _⟩ :=
    process_terminates streams.progress represented future.safe
  obtain ⟨next, nextRep, same, output, noInput⟩ :=
    process_exec_correct streams ids execution represented future
  cases same
  exact ⟨trace, final, next, execution, nextRep, output, noInput⟩

/-- From the initial state and an empty output history, some execution reads the whole input,
writes exactly the little-endian bytes of the event words of `Spec.run` from the empty book on the
whole words of the input, and returns status 0 when the input fills whole words and 28
otherwise. -/
theorem process_output {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world : World} (represented : rep position world)
    (empty : position.output = [])
    (ids : (Spec.records (leWords position.input)).length < 2 ^ 64 - 1) :
    ∃ trace final next,
      Process.Exec host process initial world trace
        (.returned (expectedStatus position.input)) final ∧
      rep next final ∧ next.output = expectedOutput position.input ∧ next.input = [] :=
  process_terminates_future streams ids represented (future_initial position empty)

end Demos.OrderBook.Process
