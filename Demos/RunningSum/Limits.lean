import Demos.RunningSum.Model
import Demos.RunningSum.TerminationTyped
import Demos.StreamFold.Observed
import Demos.StreamFold.Sizes

/-! Limits on the lines and totals of an input of the integer running sum, and the kernel
specification that carries them through a run. -/

namespace Demos.RunningSum

open LeanExe LeanExe.Wasi Verified.Wasi
open Demos.StreamFold (StreamPosition StreamHost observedStreamRep)

/-- Each line up to and including the first line without an integer has at most `L` bytes, and
`total` plus the integers of each prefix of lines with integers has at most `D` digits. -/
def LimitsFrom (L D : Nat) (total : Int) : List (Array UInt64) → Prop
  | [] => True
  | line :: rest => line.size ≤ L ∧
      (ValidLine line → integerDigitCount (total + lineInteger line) ≤ D ∧
        LimitsFrom L D (total + lineInteger line) rest)

def InputLimits (L D : Nat) (input : List UInt64) : Prop :=
  LimitsFrom L D 0 (StreamFold.Model.lines input)

/-- `kernelSpec` with the limits: a total has at most `D` digits, and a line at most `L` bytes,
after which an accepted line's total has at most `D` digits. -/
def limitSpec (L D : Nat) : StreamFold.KernelSpec lineKernel where
  Good := fun total => total.Valid ∧ total.digits.size ≤ D
  Room := fun total line => kernelSpec.Room total line ∧ line.size ≤ L ∧
    ((parse line).valid = true → (add total (parse line).value).digits.size ≤ D)
  lineFits := fun room => kernelSpec.lineFits room.1
  accepted := fun good room valid =>
    ⟨⟨(kernelSpec.accepted good.1 room.1 valid).1, room.2.2 valid⟩,
      (kernelSpec.accepted good.1 room.1 valid).2⟩
  outputBound := kernelSpec.outputBound

theorem limitRooms (L D : Nat) {lines : List (Array UInt64)} {total : Decimal}
    (normal : total.Valid) (bounds : BoundsFrom total.value lines)
    (limits : LimitsFrom L D total.value lines) :
    StreamFold.Model.LineRooms (limitSpec L D) total lines := by
  induction lines generalizing total with
  | nil => trivial
  | cons line rest ih =>
      have room := bounds.room normal
      obtain ⟨size, after⟩ := limits
      have digits : (parse line).valid = true →
          (add total (parse line).value).digits.size ≤ D := fun accepted => by
        have valid : ValidLine line :=
          (parse_valid_iff line (kernelSpec.lineFits room)).mp accepted
        obtain ⟨sumNormal, _, sumValue⟩ := kernel_accepted normal room accepted
        have bound := (after valid).1
        rw [← sumValue, decimal_digitCount _ sumNormal] at bound
        exact bound
      refine ⟨⟨room, size, digits⟩, fun accepted => ?_⟩
      have valid : ValidLine line := (parse_valid_iff line (kernelSpec.lineFits room)).mp accepted
      obtain ⟨sumNormal, _, sumValue⟩ := kernel_accepted normal room accepted
      apply ih sumNormal
      · rw [sumValue]
        exact bounds.tail valid
      · rw [sumValue]
        exact (after valid).2

/-- A bound on the bytes of the rendering of `total`. -/
def outputSize (total : Decimal) : Nat :=
  if total.digits.size + 2 < UInt64.size then total.digits.size + 2 else UInt64.size

theorem render_outputSize (number : Decimal) : (render number).data.size ≤ outputSize number := by
  unfold outputSize
  split
  · exact render_size_le number ‹_›
  · exact Nat.le_of_lt (render_size_bound number)

theorem kernel_outputSize (total : Decimal) (line : Array UInt64)
    (_ : (lineKernel total line).valid = true) :
    (lineKernel total line).output.data.size ≤ outputSize (lineKernel total line).total :=
  render_outputSize _

/-- The invariant of a run within the limits: the state has a future under `limitSpec L D`, and
its buffers are within their bounds. -/
def LimitInv (L D : Nat) (state : State) (position : StreamPosition) : Prop :=
  (∃ history expected status,
    StreamFold.StreamFuture (limitSpec L D) (bufferState state) position history expected status) ∧
  StreamFold.Within outputSize (bufferState state)

/-- The sizes of a state within the limits: a total of at most `D` digits, a line of at most `L`
bytes, an input buffer of at most 4,096 bytes, and an output buffer of at most `D + 2` bytes. -/
structure Sized (L D : Nat) (state : State) : Prop where
  total : state.total.digits.size ≤ D
  line : state.line.size ≤ L
  input : state.input.data.size ≤ 4096
  output : state.output.data.size ≤ D + 2

theorem sized_of_within {L D : Nat} {state : State} (small : D + 2 < UInt64.size)
    (total : state.total.digits.size ≤ D) (line : state.line.size ≤ L)
    (within : StreamFold.Within outputSize (bufferState state)) : Sized L D state := by
  refine ⟨total, line, within.input, ?_⟩
  have output : state.output.data.size ≤ outputSize state.total := within.output
  have fits : state.total.digits.size + 2 < UInt64.size := by omega
  simp only [outputSize, fits, ↓reduceIte] at output
  omega

theorem LimitInv.sized {L D : Nat} {state : State} {position : StreamPosition}
    (invariant : LimitInv L D state position) (small : D + 2 < UInt64.size) : Sized L D state :=
  let ⟨⟨_, _, _, future⟩, within⟩ := invariant
  sized_of_within small future.normal.2
    (StreamFold.StreamFuture.line_le (limitSpec L D) L (fun room => room.2.1) future) within

theorem limitInv_initial (L D : Nat) (position : StreamPosition) (empty : position.output = [])
    (bounds : InputBounds position.input) (limits : InputLimits L D position.input) :
    LimitInv L D initial position := by
  have rooms := limitRooms L D zero_valid bounds limits
  exact ⟨⟨_, _, _, StreamFold.streamFuture_initial (limitSpec L D) zero position empty
    ⟨zero_valid, Nat.zero_le _⟩ rooms⟩, StreamFold.Within.initial outputSize zero⟩

theorem limit_advances {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) (L D : Nat) :
    Termination.StepAdvances (observedHost host) (observedStreamRep rep)
      (fun position => position.input.length) StreamPosition.zeroWrites (LimitInv L D) := by
  intro state position world final trace next _ invariant represented execution
  obtain ⟨⟨history, expected, status, future⟩, within⟩ := invariant
  obtain ⟨mapped, mappedExecution, related⟩ := (buffer_step_related state).exec _ _ _ _ execution
  cases related with
  | returned values =>
      obtain ⟨nextPosition, nextRep, continued, _⟩ :=
        StreamFold.streamFuture_step (limitSpec L D) streams.observed represented future
          mappedExecution
      have nextWithin := StreamFold.step_within kernel_outputSize within mappedExecution
      refine ⟨nextPosition, nextRep, fun running => ?_⟩
      obtain ⟨smaller, nextHistory, nextFuture⟩ := continued (values.running.symm.trans running)
      refine ⟨⟨⟨nextHistory, expected, status, ?_⟩, ?_⟩, ?_⟩
      · simpa only [values.state] using nextFuture
      · simpa only [values.state] using nextWithin
      · simpa only [Termination.rank, values.state] using smaller

/-- Every state that a step from a state within the limits returns, running or stopped, has the
sizes of the limits. -/
theorem step_sized {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {L D : Nat} (small : D + 2 < UInt64.size) {state : State}
    {position : StreamPosition} {world final : Observed World} {trace : List Event}
    {next : ProcessStep State} (invariant : LimitInv L D state position)
    (represented : observedStreamRep rep position world)
    (execution : LeanExe.Wasi.Exec (observedHost host) (step state) world trace (.returned next)
      final) : Sized L D next.state := by
  obtain ⟨⟨history, expected, status, future⟩, within⟩ := invariant
  obtain ⟨mapped, mappedExecution, related⟩ := (buffer_step_related state).exec _ _ _ _ execution
  cases related with
  | returned values =>
      have nextWithin := StreamFold.step_within kernel_outputSize within mappedExecution
      rw [values.state] at nextWithin
      cases running : next.running with
      | true =>
          obtain ⟨nextPosition, _, continued, _⟩ :=
            StreamFold.streamFuture_step (limitSpec L D) streams.observed represented future
              mappedExecution
          obtain ⟨_, nextHistory, nextFuture⟩ := continued (values.running.symm.trans running)
          rw [values.state] at nextFuture
          exact sized_of_within small nextFuture.normal.2
            (StreamFold.StreamFuture.line_le (limitSpec L D) L (fun room => room.2.1) nextFuture)
            nextWithin
      | false =>
          have stopped := StreamFold.streamFuture_stopped (limitSpec L D) L (fun room => room.2.1)
            future mappedExecution (values.running.symm.trans running)
          rw [values.state] at stopped
          exact sized_of_within small stopped.1.2 stopped.2 nextWithin

end Demos.RunningSum
