import Demos.Rcv.ProcessFuture

/-! The correctness of [the tabulator's process](Process.lean) under StreamFold's host assumptions.
`process_output` states that every run of `begin` on an input of at most `limit` bytes, from an
empty output history, returns the running state of the report of the input, from which some
execution of the process writes exactly the bytes of the report, the requirements' `report b` for
the bytes `b` of the input, and returns status 0.  `process_exec_correct` states that every
finite execution from a state with the invariant `Writes expected` returns status 0 after writing
`expected`, and `process_terminates` of [the control](ProcessControl.lean) gives an execution that
returns. -/

namespace Demos.Rcv.Process

open LeanExe LeanExe.Wasi
open Demos.StreamFold (StreamPosition StreamHost)

/-- Every finite execution from a state with the invariant returns status 0, after writing exactly
the bytes of `expected`, with the whole input read. -/
theorem process_exec_correct {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {expected : List UInt64} {maxOutput : Nat} {s : State} {world final : World}
    {trace : List Event} {outcome : Outcome UInt64}
    (execution : Process.Exec host process s world trace outcome final)
    {position : StreamPosition} (represented : rep position world)
    (future : Writes expected maxOutput s position) :
    ∃ next, rep next final ∧ outcome = .returned 0 ∧
      next.output = expected ∧ next.input = [] := by
  induction execution generalizing position with
  | done execution stopped =>
      obtain ⟨next, nextRep, _, finished⟩ := future_step streams represented future execution
      obtain ⟨status, output, noInput⟩ := finished stopped
      exact ⟨next, nextRep, congrArg Outcome.returned status, output, noInput⟩
  | next execution running continuation ih =>
      obtain ⟨next, nextRep, continued, _⟩ := future_step streams represented future execution
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
bytes of `expected`, with the whole input read. -/
theorem process_terminates_future {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {expected : List UInt64} {maxOutput : Nat} {s : State} {position : StreamPosition}
    {world : World} (represented : rep position world)
    (future : Writes expected maxOutput s position) :
    ∃ trace final next,
      Process.Exec host process s world trace (.returned 0) final ∧
      rep next final ∧ next.output = expected ∧ next.input = [] := by
  obtain ⟨trace, final, _, execution, _⟩ :=
    process_terminates streams.progress represented future.safe
  obtain ⟨next, nextRep, _, output, noInput⟩ :=
    process_exec_correct streams execution represented future
  exact ⟨trace, final, next, execution, nextRep, output, noInput⟩

/-- Every run of `begin` on an input of at most `limit` bytes from an empty output history
returns a running state with status 0, from which some execution of the process writes exactly
the bytes of the report of the input and returns status 0. -/
theorem process_output {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world : World} (represented : rep position world)
    (empty : position.output = []) (size : position.input.length ≤ limit.toNat)
    {trace : List Event} {outcome : Outcome (ProcessStep State)} {after : World}
    (started : LeanExe.Wasi.Exec host begin world trace outcome after) :
    ∃ first, outcome = .returned first ∧ first.running = true ∧ first.status = 0 ∧
      ∃ rest final next,
        Process.Exec host process first.state after rest (.returned 0) final ∧
        rep next final ∧ next.output = expectedOutput position.input ∧ next.input = [] := by
  obtain ⟨first, firstPosition, same, firstRep, running, status, future⟩ :=
    begin_report streams size empty represented started
  exact ⟨first, same, running, status, process_terminates_future streams firstRep future⟩

end Demos.Rcv.Process
