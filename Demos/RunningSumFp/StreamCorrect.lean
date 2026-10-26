import Demos.RunningSumFp.Model
import Demos.StreamFold.Correct
import Demos.StreamFold.Observed
import Verified.Wasi.ProcessEntryProofs

namespace Demos.RunningSumFp

open LeanExe LeanExe.Wasi Verified.Wasi
open Library.Numerics.Decimal
open Library.Numerics.Decimal.Shared.StrconvGrammar
open Demos.StreamFold (StreamPosition StreamHost observedStreamRep stdoutWords)

def printedBytes (word : UInt64) : List UInt8 :=
  (PrintFloat.print64 word).toList.map UInt64.toUInt8 ++ [10]

noncomputable def cumulativeOutput (numbers : List Num) : List UInt64 :=
  ((prefixBits 0 numbers).flatMap printedBytes).map UInt8.toUInt64

theorem render_printedBytes (value : Float) :
    (render value).data.data.toList = printedBytes value.toBits := by
  obtain ⟨text, number, printed, _, _, output⟩ := render_text value
  simpa [printedBytes, printed, words, List.map_map, Function.comp_def] using output

theorem outputWords_fp (numbers : List Num) :
    StreamFold.outputWords ((prefixFloats 0 numbers).map render) = cumulativeOutput numbers := by
  have bits := prefixFloats_bits (0 : Float) numbers
  rw [zero_bits] at bits
  unfold cumulativeOutput
  rw [← bits, List.flatMap_map]
  simp only [StreamFold.outputWords, List.flatMap_map, StreamFold.byteWords, render_printedBytes]
  rw [List.map_flatMap]

/-- `numbers` holds the numbers of the input lines before the first line that denotes no number,
and `status` is 0 when every line denotes a number and 28 otherwise. -/
abbrev InputValues (input : List UInt64) (numbers : List Num) (status : UInt64) : Prop :=
  StreamFold.Model.LineValues InputLine (StreamFold.Model.lines input) numbers status

theorem inputValues_exist {input : List UInt64} (short : ShortLines input) :
    ∃ numbers status, InputValues input numbers status := by
  obtain ⟨numbers, status, values, _⟩ := foldOutcome_fp short (0 : Float)
  exact ⟨numbers, status, values⟩

theorem inputValues_unique {input : List UInt64} {numbers others : List Num} {status other : UInt64}
    (first : InputValues input numbers status) (second : InputValues input others other) :
    numbers = others ∧ status = other :=
  StreamFold.Model.LineValues.unique (Denotes := InputLine) inputLine_unique first second

theorem foldOutcome_input {input : List UInt64} {numbers : List Num} {status : UInt64}
    (short : ShortLines input) (values : InputValues input numbers status) :
    StreamFold.Model.foldOutcome lineKernel 0 (StreamFold.Model.lines input) =
      ((prefixFloats 0 numbers).map render, status) := by
  obtain ⟨found, code, foundValues, folded⟩ := foldOutcome_fp short (0 : Float)
  obtain ⟨rfl, rfl⟩ := inputValues_unique foundValues values
  exact folded

theorem process_fp_correct {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : World} {trace : List Event}
    {outcome : Outcome UInt64} (represented : rep position world) (empty : position.output = [])
    (short : ShortLines position.input) {numbers : List Num} {status : UInt64}
    (values : InputValues position.input numbers status)
    (execution : Process.Exec host process initial world trace outcome final) :
    ∃ nextPosition, rep nextPosition final ∧ outcome = .returned status ∧
      nextPosition.output = cumulativeOutput numbers ∧ (status = 0 → nextPosition.input = []) := by
  have future := StreamFold.streamFuture_initial kernelSpec (0 : Float) position empty
    True.intro (lineRooms short 0)
  rw [foldOutcome_input short values] at future
  have shared := buffer_related.exec (a := initial) (b := StreamFold.initial (0 : Float))
    buffer_initial.symm execution
  obtain ⟨nextPosition, nextRep, returned, done⟩ :=
    StreamFold.process_exec_correct kernelSpec streams shared represented future
  exact ⟨nextPosition, nextRep, returned, done.output.trans (outputWords_fp numbers), done.input⟩

theorem process_terminates_fp {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world : World} (represented : rep position world)
    (empty : position.output = []) (short : ShortLines position.input) :
    ∃ numbers status, InputValues position.input numbers status ∧
      ∃ trace final nextPosition, Process.Exec host process initial world trace (.returned status) final ∧
        rep nextPosition final ∧ nextPosition.output = cumulativeOutput numbers ∧
        (status = 0 → nextPosition.input = []) := by
  obtain ⟨numbers, status, values⟩ := inputValues_exist short
  obtain ⟨trace, final, nextPosition, shared, nextRep, done⟩ :=
    StreamFold.initial_terminates_output kernelSpec streams (0 : Float) represented empty
      True.intro (lineRooms short 0)
  rw [foldOutcome_input short values] at shared done
  exact ⟨numbers, status, values, trace, final, nextPosition,
    buffer_related.exec_back buffer_initial.symm shared, nextRep,
    done.output.trans (outputWords_fp numbers), done.input⟩

def CommandFPResult {World : Type} (host : Host World)
    (rep : StreamPosition → World → Prop) (numbers : List Num) (status : UInt64)
    (outcome : Outcome Unit) (final : Observed World) : Prop :=
  stdoutWords final.events = cumulativeOutput numbers ∧
    ∃ before position, observedStreamRep rep position before ∧
      position.output = cumulativeOutput numbers ∧
      ((outcome = .exited status ∧ (observedHost host).exit before status final) ∨
        ∃ message, outcome = .trapped message ∧
          (observedHost host).exitTrap before status message final)

theorem command_fp {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : Observed World} {trace : List Event}
    {outcome : Outcome Unit} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (short : ShortLines position.input) {numbers : List Num} {status : UInt64}
    (values : InputValues position.input numbers status)
    (execution : ProcessCommandExec (observedHost host) begin process world trace outcome final) :
    CommandFPResult host rep numbers status outcome final := by
  have observed : observedStreamRep rep position world :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  cases execution with
  | next started continued finished =>
      change LeanExe.Wasi.Exec (observedHost host) (.pure (⟨true, 0, initial⟩ : ProcessStep State))
        _ _ _ _ at started
      cases started
      change Process.Exec (observedHost host) process initial _ _ _ _ at continued
      obtain ⟨nextPosition, nextRep, returned, output, _⟩ :=
        process_fp_correct streams.observed observed empty short values continued
      cases returned
      change LeanExe.Wasi.Exec (observedHost host) (Action.exit (α := Unit) status)
        _ _ _ _ at finished
      have code := values.exitStatus
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

end Demos.RunningSumFp
