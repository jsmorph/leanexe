import Demos.Rcv.ProcessFuture
import Demos.Rcv.ProcessProof
import Verified.ChargeFacts

/-! The sizes that the charges of the compiled process need.  `Sized L` states the sizes of a
reached state for an input of at most `L` bytes: an input buffer of at most `L` bytes and a report
of at most `outputLimit` bytes, and `copyLimit L` bounds the copy of such a state.  `step_sized`
states that a step from a state with the invariant `Future` returns a state with these sizes. -/

namespace Demos.Rcv.Process

open LeanExe LeanExe.Wasi Verified
open Demos.StreamFold (StreamPosition StreamHost)

/-- The bytes of a copy of a state. -/
def copyBytes (s : State) : Nat :=
  Bytes.allocationCost s.input.data.size + Bytes.allocationCost s.output.data.size

theorem state_copyCost (s : State) : stateTy.copyCost (sourceState s) = copyBytes s := by
  simp only [stateTy, sourceState, Ty.copyCost, copyBytes]
  omega

/-- The sizes of a reached state for an input of at most `L` bytes. -/
structure Sized (L : Nat) (s : State) : Prop where
  input : s.input.data.size ≤ L
  output : s.output.data.size ≤ outputLimit

/-- A bound on the copy of a state with the sizes of `Sized L`: an input block of at most `L + 55`
bytes and a report block of at most `outputLimit + 55` bytes. -/
def copyLimit (L : Nat) : Nat := L + 1301140

theorem Sized.copyCost {L : Nat} {s : State} (sized : Sized L s) :
    stateTy.copyCost (sourceState s) ≤ copyLimit L := by
  rw [state_copyCost]
  have input := allocationCost_le s.input.data.size
  have output := allocationCost_le s.output.data.size
  have := sized.input
  have := sized.output
  simp only [copyBytes, copyLimit, outputLimit] at *
  omega

theorem Future.sized {input : List UInt64} {L : Nat} (size : input.length ≤ L) {s : State}
    {position : StreamPosition} (future : Future input s position) : Sized L s :=
  ⟨Nat.le_trans future.inputSize size, future.outputSize⟩

/-- A step under `StreamProgress` that stops returns the state it started from. -/
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
  · cases eof : s.eof with
    | false =>
        rw [step_read pending eof] at execution
        change LeanExe.Wasi.Exec host (.read 4096 fun reply => .pure (afterRead s reply))
          world trace (.returned next) final at execution
        cases execution with
        | read_reject capacity continuation =>
            exact False.elim ((by decide : ¬ 2 ^ 32 ≤ (4096 : UInt64).toNat) capacity)
        | read_return capacity operation continuation =>
            cases continuation
            obtain ⟨bytes, _, replyEq, _, _, _⟩ := progress.read_reply ready operation
            cases replyEq
            simp only [readResult, ↓reduceIte] at stopped
            rw [(afterRead_running s _).1] at stopped
            cases stopped
    | true =>
        rw [step_stop pending eof] at execution
        cases execution
        rfl

/-- Every state that a step from a state with the invariant returns, running or stopped, has the
sizes of `Sized L` for an input of at most `L` bytes. -/
theorem step_sized {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {input : List UInt64} (short : input.length < 2 ^ 32)
    {L : Nat} (size : input.length ≤ L)
    {s : State} {position : StreamPosition}
    {world final : World} {trace : List Event} {next : ProcessStep State}
    (represented : rep position world) (future : Future input s position)
    (execution : LeanExe.Wasi.Exec host (step s) world trace (.returned next) final) :
    Sized L next.state := by
  cases running : next.running with
  | true =>
      obtain ⟨_, _, continued, _⟩ := future_step streams short represented future execution
      exact (continued running).sized size
  | false =>
      rw [step_stopped_state streams.progress represented future.safe execution running]
      exact future.sized size

end Demos.Rcv.Process
