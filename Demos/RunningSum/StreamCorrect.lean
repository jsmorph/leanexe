import Demos.RunningSum.Model
import Demos.RunningSum.Termination
import Demos.StreamFold.Correct
import Demos.StreamFold.Observed
import Verified.Wasi.ProcessEntryProofs

namespace Demos.RunningSum

open LeanExe LeanExe.Wasi Verified.Wasi
open Demos.StreamFold (StreamPosition StreamHost observedStreamRep stdoutWords)

def integerWords (value : Int) : List UInt64 := (integerEncoding value).map UInt8.toUInt64

def cumulativeOutput (values : List Int) : List UInt64 :=
  (prefixTotals 0 values).flatMap integerWords

theorem outputWords_correct {values : List Int} {output : List Bytes}
    (encoded : List.Forall₂ DecimalOutput values output) :
    StreamFold.outputWords output = values.flatMap integerWords := by
  induction encoded with
  | nil => rfl
  | cons same rest ih =>
      change StreamFold.byteWords _ ++ StreamFold.outputWords _ = integerWords _ ++ _
      rw [ih]
      unfold StreamFold.byteWords integerWords
      rw [same]
      rfl

/-- `values` holds the integers of the input lines before the first line that is not a decimal
integer, and `status` is 0 when every line is one and 28 otherwise. -/
abbrev InputValues (input : List UInt64) (values : List Int) (status : UInt64) : Prop :=
  StreamFold.Model.LineValues DecimalLine (StreamFold.Model.lines input) values status

theorem inputValues_exist {input : List UInt64} (bounds : InputBounds input) :
    ∃ values status, InputValues input values status := by
  obtain ⟨values, status, lineValues, _⟩ := foldOutcome_integer zero_valid bounds
  exact ⟨values, status, lineValues⟩

theorem inputValues_unique {input : List UInt64} {values others : List Int} {status other : UInt64}
    (first : InputValues input values status) (second : InputValues input others other) :
    values = others ∧ status = other :=
  StreamFold.Model.LineValues.unique (Denotes := DecimalLine) decimalLine_unique first second

theorem foldOutcome_input {input : List UInt64} {values : List Int} {status : UInt64}
    (bounds : InputBounds input) (lineValues : InputValues input values status) :
    ∃ outputs, StreamFold.Model.foldOutcome lineKernel zero (StreamFold.Model.lines input) =
      (outputs, status) ∧ StreamFold.outputWords outputs = cumulativeOutput values := by
  obtain ⟨found, code, foundValues, outputs, folded, encoded⟩ :=
    foldOutcome_integer zero_valid bounds
  obtain ⟨rfl, rfl⟩ := inputValues_unique foundValues lineValues
  exact ⟨outputs, folded, outputWords_correct encoded⟩

theorem process_exec_integer {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : World} {trace : List Event}
    {outcome : Outcome UInt64} (represented : rep position world) (empty : position.output = [])
    (bounds : InputBounds position.input) {values : List Int} {status : UInt64}
    (lineValues : InputValues position.input values status)
    (execution : Process.Exec host process initial world trace outcome final) :
    ∃ nextPosition, rep nextPosition final ∧ outcome = .returned status ∧
      nextPosition.output = cumulativeOutput values ∧ (status = 0 → nextPosition.input = []) := by
  obtain ⟨outputs, folded, output⟩ := foldOutcome_input bounds lineValues
  have future := StreamFold.streamFuture_initial kernelSpec zero position empty zero_valid
    (lineRooms zero_valid bounds)
  rw [folded] at future
  have shared := buffer_related.exec (a := initial) (b := StreamFold.initial zero)
    buffer_initial.symm execution
  obtain ⟨nextPosition, nextRep, returned, done⟩ :=
    StreamFold.process_exec_correct kernelSpec streams shared represented future
  exact ⟨nextPosition, nextRep, returned, done.output.trans output, done.input⟩

theorem process_terminates_integer {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world : World} (represented : rep position world)
    (empty : position.output = []) (bounds : InputBounds position.input) :
    ∃ values status, InputValues position.input values status ∧
      ∃ trace final nextPosition, Process.Exec host process initial world trace (.returned status) final ∧
        rep nextPosition final ∧ nextPosition.output = cumulativeOutput values ∧
        (status = 0 → nextPosition.input = []) := by
  obtain ⟨values, status, lineValues⟩ := inputValues_exist bounds
  obtain ⟨outputs, folded, output⟩ := foldOutcome_input bounds lineValues
  obtain ⟨trace, final, nextPosition, shared, nextRep, done⟩ :=
    StreamFold.initial_terminates_output kernelSpec streams zero represented empty zero_valid
      (lineRooms zero_valid bounds)
  rw [folded] at shared done
  exact ⟨values, status, lineValues, trace, final, nextPosition,
    buffer_related.exec_back buffer_initial.symm shared, nextRep, done.output.trans output,
    done.input⟩

def CommandIntegerResult {World : Type} (host : Host World)
    (rep : StreamPosition → World → Prop) (values : List Int) (status : UInt64)
    (outcome : Outcome Unit) (final : Observed World) : Prop :=
  stdoutWords final.events = cumulativeOutput values ∧
    ∃ before position, observedStreamRep rep position before ∧
      position.output = cumulativeOutput values ∧
      ((outcome = .exited status ∧ (observedHost host).exit before status final) ∨
        ∃ message, outcome = .trapped message ∧
          (observedHost host).exitTrap before status message final)

theorem command_integer {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : Observed World} {trace : List Event}
    {outcome : Outcome Unit} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (bounds : InputBounds position.input) {values : List Int} {status : UInt64}
    (lineValues : InputValues position.input values status)
    (execution : ProcessCommandExec (observedHost host) begin process world trace outcome final) :
    CommandIntegerResult host rep values status outcome final := by
  have observed : observedStreamRep rep position world :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  cases execution with
  | next started continued finished =>
      change LeanExe.Wasi.Exec (observedHost host) (.pure (⟨true, 0, initial⟩ : ProcessStep State))
        _ _ _ _ at started
      cases started
      change Process.Exec (observedHost host) process initial _ _ _ _ at continued
      obtain ⟨nextPosition, nextRep, returned, output, _⟩ :=
        process_exec_integer streams.observed observed empty bounds lineValues continued
      cases returned
      change LeanExe.Wasi.Exec (observedHost host) (Action.exit (α := Unit) status)
        _ _ _ _ at finished
      have code := lineValues.exitStatus
      cases finished with
      | exit accepted =>
          have finalOutput := StreamFold.observedStreamRep_exit_output nextRep accepted
          rw [code] at accepted ⊢
          exact ⟨finalOutput.symm.trans output, _, nextPosition, nextRep, output, Or.inl ⟨rfl, accepted⟩⟩
      | exitTrap rejected =>
          have finalOutput := StreamFold.observedStreamRep_exitTrap_output nextRep rejected
          rw [code] at rejected
          exact ⟨finalOutput.symm.trans output, _, nextPosition, nextRep, output,
            Or.inr ⟨_, rfl, rejected⟩⟩
  | beginExit execution =>
      change LeanExe.Wasi.Exec (observedHost host) (.pure (⟨true, 0, initial⟩ : ProcessStep State))
        _ _ _ _ at execution
      cases execution
  | beginTrap execution =>
      change LeanExe.Wasi.Exec (observedHost host) (.pure (⟨true, 0, initial⟩ : ProcessStep State))
        _ _ _ _ at execution
      cases execution

end Demos.RunningSum
