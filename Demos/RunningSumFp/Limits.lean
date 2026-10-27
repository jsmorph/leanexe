import Demos.RunningSumFp.Model
import Demos.RunningSumFp.TerminationTyped
import Demos.RunningSumFp.PrintCharges
import Demos.StreamFold.Observed
import Demos.StreamFold.Sizes

/-! A limit on the lines of an input of the binary64 running sum, and the kernel specification
that carries it through a run. -/

namespace Demos.RunningSumFp

open LeanExe LeanExe.Wasi Verified.Wasi
open Library.Numerics.Decimal.Shared.StrconvGrammar
open Demos.StreamFold (StreamPosition StreamHost observedStreamRep)

/-- Each line up to and including the first line that denotes no number has at most `L`
bytes. -/
def LimitsFrom (L : Nat) : List (Array UInt64) → Prop
  | [] => True
  | line :: rest => line.size ≤ L ∧ ((∃ number, InputLine line number) → LimitsFrom L rest)

def InputLimits (L : Nat) (input : List UInt64) : Prop :=
  LimitsFrom L (StreamFold.Model.lines input)

/-- `kernelSpec` with the limit: a line has at most `L` bytes. -/
def limitSpec (L : Nat) : StreamFold.KernelSpec lineKernel where
  Good := fun _ => True
  Room := fun total line => kernelSpec.Room total line ∧ line.size ≤ L
  lineFits := fun room => kernelSpec.lineFits room.1
  accepted := fun good room valid => kernelSpec.accepted good room.1 valid
  outputBound := kernelSpec.outputBound

theorem limitRooms (L : Nat) {lines : List (Array UInt64)}
    (short : ∀ line ∈ lines, ∃ text : List UInt8, line = words text ∧ text.length < 2 ^ 32)
    (limits : LimitsFrom L lines) (total : Float) :
    StreamFold.Model.LineRooms (limitSpec L) total lines := by
  induction lines generalizing total with
  | nil => trivial
  | cons line rest ih =>
      obtain ⟨text, rfl, bound⟩ := short _ (List.mem_cons_self ..)
      obtain ⟨size, after⟩ := limits
      refine ⟨⟨show (words text).size < 2 ^ 32 by simpa [words] using bound, size⟩,
        fun accepted => ?_⟩
      apply ih (fun line member => short line (List.mem_cons_of_mem _ member))
      apply after
      by_contra none
      have invalid : ∀ number, ¬ LineDenotes text number :=
        fun number meaning => none ⟨number, text, rfl, bound, meaning⟩
      have rejected := parse_reject text bound invalid
      simp [lineKernel, rejected] at accepted

/-- A bound on the bytes of the rendering of a total. -/
def outputSize (_ : Float) : Nat := 43

theorem render_size_le (value : Float) : (render value).data.size ≤ 43 := by
  have size := print64_size_le value.toBits
  have small := Verified.toUInt64_toNat_le (Library.Numerics.Decimal.PrintFloat.print64 value.toBits).size
  unfold render
  dsimp only
  rw [LeanExe.Bytes.data_size_build, UInt64.toNat_add, UInt64.toNat_one]
  omega

theorem kernel_outputSize (total : Float) (line : Array UInt64)
    (_ : (lineKernel total line).valid = true) :
    (lineKernel total line).output.data.size ≤ outputSize (lineKernel total line).total :=
  render_size_le _

/-- The invariant of a run within the limit: the state has a future under `limitSpec L`, and its
buffers are within their bounds. -/
def LimitInv (L : Nat) (state : State) (position : StreamPosition) : Prop :=
  (∃ history expected status,
    StreamFold.StreamFuture (limitSpec L) (bufferState state) position history expected status) ∧
  StreamFold.Within outputSize (bufferState state)

/-- The sizes of a state within the limit: a line of at most `L` bytes, an input buffer of at
most 4,096 bytes, and an output buffer of at most 43 bytes. -/
structure Sized (L : Nat) (state : State) : Prop where
  line : state.line.size ≤ L
  input : state.input.data.size ≤ 4096
  output : state.output.data.size ≤ 43

theorem sized_of_within {L : Nat} {state : State} (line : state.line.size ≤ L)
    (within : StreamFold.Within outputSize (bufferState state)) : Sized L state :=
  ⟨line, within.input, within.output⟩

theorem LimitInv.sized {L : Nat} {state : State} {position : StreamPosition}
    (invariant : LimitInv L state position) : Sized L state :=
  let ⟨⟨_, _, _, future⟩, within⟩ := invariant
  sized_of_within (StreamFold.StreamFuture.line_le (limitSpec L) L (fun room => room.2) future)
    within

theorem limitInv_initial (L : Nat) (position : StreamPosition) (empty : position.output = [])
    (short : ShortLines position.input) (limits : InputLimits L position.input) :
    LimitInv L initial position := by
  have rooms := limitRooms L short limits (0 : Float)
  exact ⟨⟨_, _, _, StreamFold.streamFuture_initial (limitSpec L) (0 : Float) position empty
    trivial rooms⟩, StreamFold.Within.initial outputSize (0 : Float)⟩

theorem limit_advances {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) (L : Nat) :
    Termination.StepAdvances (observedHost host) (observedStreamRep rep)
      (fun position => position.input.length) StreamPosition.zeroWrites (LimitInv L) := by
  intro state position world final trace next _ invariant represented execution
  obtain ⟨⟨history, expected, status, future⟩, within⟩ := invariant
  obtain ⟨mapped, mappedExecution, related⟩ := (buffer_step_related state).exec _ _ _ _ execution
  cases related with
  | returned values =>
      obtain ⟨nextPosition, nextRep, continued, _⟩ :=
        StreamFold.streamFuture_step (limitSpec L) streams.observed represented future
          mappedExecution
      have nextWithin := StreamFold.step_within kernel_outputSize within mappedExecution
      refine ⟨nextPosition, nextRep, fun running => ?_⟩
      obtain ⟨smaller, nextHistory, nextFuture⟩ := continued (values.running.symm.trans running)
      refine ⟨⟨⟨nextHistory, expected, status, ?_⟩, ?_⟩, ?_⟩
      · simpa only [values.state] using nextFuture
      · simpa only [values.state] using nextWithin
      · simpa only [Termination.rank, values.state] using smaller

/-- Every state that a step from a state within the limit returns, running or stopped, has the
sizes of the limit. -/
theorem step_sized {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {L : Nat} {state : State}
    {position : StreamPosition} {world final : Observed World} {trace : List Event}
    {next : ProcessStep State} (invariant : LimitInv L state position)
    (represented : observedStreamRep rep position world)
    (execution : LeanExe.Wasi.Exec (observedHost host) (step state) world trace (.returned next)
      final) : Sized L next.state := by
  obtain ⟨⟨history, expected, status, future⟩, within⟩ := invariant
  obtain ⟨mapped, mappedExecution, related⟩ := (buffer_step_related state).exec _ _ _ _ execution
  cases related with
  | returned values =>
      have nextWithin := StreamFold.step_within kernel_outputSize within mappedExecution
      rw [values.state] at nextWithin
      cases running : next.running with
      | true =>
          obtain ⟨nextPosition, _, continued, _⟩ :=
            StreamFold.streamFuture_step (limitSpec L) streams.observed represented future
              mappedExecution
          obtain ⟨_, nextHistory, nextFuture⟩ := continued (values.running.symm.trans running)
          rw [values.state] at nextFuture
          exact sized_of_within
            (StreamFold.StreamFuture.line_le (limitSpec L) L (fun room => room.2) nextFuture)
            nextWithin
      | false =>
          have stopped := StreamFold.streamFuture_stopped (limitSpec L) L (fun room => room.2)
            future mappedExecution (values.running.symm.trans running)
          rw [values.state] at stopped
          exact sized_of_within stopped.2 nextWithin

end Demos.RunningSumFp
