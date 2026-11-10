import Demos.Rcv.ProcessFuture
import Demos.Rcv.ProcessProof
import Verified.ChargeFacts

/-! The sizes that the charges of the compiled process need.  `Sized` states that a state holds a
report of at most `outputLimit` bytes, and `copyLimit` bounds the copy of such a state.
`step_sized` states that a step from a state with the invariant `Future` returns a state with this
size, and `started_sized` that every state that `begin` returns has it. -/

namespace Demos.Rcv.Process

open LeanExe LeanExe.Wasi Verified
open Demos.StreamFold (StreamPosition StreamHost)

/-- The bytes of a copy of a state. -/
def copyBytes (s : State) : Nat := Bytes.allocationCost s.output.data.size

theorem state_copyCost (s : State) : stateTy.copyCost (sourceState s) = copyBytes s := by
  simp only [stateTy, sourceState, Ty.copyCost, copyBytes]
  omega

/-- The size of a state: a report of at most `outputLimit` bytes. -/
structure Sized (s : State) : Prop where
  output : s.output.data.size ≤ outputLimit

/-- A bound on the copy of a state with the size of `Sized`: a report block of at most
`outputLimit + 55` bytes. -/
def copyLimit : Nat := 1301085

theorem Sized.copyCost {s : State} (sized : Sized s) :
    stateTy.copyCost (sourceState s) ≤ copyLimit := by
  rw [state_copyCost]
  have output := allocationCost_le s.output.data.size
  have := sized.output
  simp only [copyBytes, copyLimit, outputLimit] at *
  omega

theorem Future.sized {input : List UInt64} {s : State} {position : StreamPosition}
    (future : Future input s position) : Sized s :=
  ⟨future.outputSize⟩

theorem initial_sized : Sized initial := ⟨Nat.zero_le _⟩

/-- Every state that `started` returns on an input of fewer than `2 ^ 32` bytes has the size of
`Sized`. -/
theorem started_sized (input : ReadResult) (small : input.bytes.data.size < 2 ^ 32) :
    Sized (started input).state := by
  unfold started
  split
  · exact initial_sized
  · split
    · exact initial_sized
    · refine ⟨?_⟩
      show (TabulateProgram.tabulate input.bytes).data.size ≤ outputLimit
      have bound := TabulateProgram.reportFile_length_le (ReadProgram.bytesOf input.bytes)
      rw [← TabulateProgram.tabulate_eq input.bytes small, ReadProgram.bytesOf_length] at bound
      exact bound

/-- A step that stops returns the state it started from. -/
theorem step_stopped_state {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat}
    (progress : Demos.StreamFold.StreamProgress host rep unread zeroWrites)
    {s : State} {ghost : Ghost} {world final : World} {trace : List Event}
    {next : ProcessStep State} (ready : rep ghost world) (safe : Safe s)
    (execution : LeanExe.Wasi.Exec host (step s) world trace (.returned next) final)
    (stopped : next.running = false) : next.state = s := by
  by_cases pending : s.written < s.output.size
  · rw [step_write pending] at execution
    change LeanExe.Wasi.Exec host
      (.write .stdout (remainingOutput s) fun reply => .pure (afterWrite s reply))
      world trace (.returned next) final at execution
    cases execution with
    | write_return operation continuation =>
        cases continuation
        obtain ⟨count, _, replyEq, _, _, _⟩ :=
          progress.write_reply ready (remainingOutput_nonempty safe pending) operation
        cases replyEq
        simp only [writeResult, ↓reduceIte] at stopped
        rw [(afterWrite_running s _).1] at stopped
        cases stopped
  · rw [step_stop pending] at execution
    cases execution
    rfl

/-- Every state that a step from a state with the invariant returns, running or stopped, has the
size of `Sized`. -/
theorem step_sized {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {input : List UInt64}
    {s : State} {position : StreamPosition}
    {world final : World} {trace : List Event} {next : ProcessStep State}
    (represented : rep position world) (future : Future input s position)
    (execution : LeanExe.Wasi.Exec host (step s) world trace (.returned next) final) :
    Sized next.state := by
  cases running : next.running with
  | true =>
      obtain ⟨_, _, continued, _⟩ := future_step streams represented future execution
      exact (continued running).sized
  | false =>
      rw [step_stopped_state streams.progress represented future.safe execution running]
      exact future.sized

end Demos.Rcv.Process
