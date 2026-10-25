import Demos.RunningSumFp.Model
import Demos.StreamFold.Correct
import Demos.RunningSum.StreamObserved
import Verified.Wasi.ProcessEntryProofs

namespace Demos.RunningSumFp

open LeanExe LeanExe.Wasi Verified.Wasi
open Library.Numerics.Decimal
open Library.Numerics.Decimal.Shared.StrconvGrammar
open Demos.RunningSum (StreamPosition StreamHost observedStreamRep stdoutWords)

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

theorem model_completion {input : List UInt64} {numbers : List Num}
    (valid : ValidInput input numbers) :
    ∃ processed final,
      StreamFold.Model.consume lineKernel (StreamFold.Model.initial (0 : Float)) input =
        .ok processed ∧
      StreamFold.Model.finish lineKernel processed = .ok final ∧
      final.output = (prefixFloats 0 numbers).map render := by
  have completed := model_fp_correct valid
  cases consumed : StreamFold.Model.consume lineKernel (StreamFold.Model.initial (0 : Float)) input with
  | error code => simp [consumed, bind, Except.bind] at completed
  | ok processed =>
      exact ⟨processed, ⟨finalTotal 0 numbers, #[], (prefixFloats 0 numbers).map render⟩,
        rfl, by simpa [consumed, bind, Except.bind] using completed, rfl⟩

theorem process_fp_correct {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : World} {trace : List Event}
    {outcome : Outcome UInt64} (represented : rep position world) (empty : position.output = [])
    (numbers : List Num) (valid : ValidInput position.input numbers)
    (execution : Process.Exec host process initial world trace outcome final) :
    ∃ nextPosition, rep nextPosition final ∧ outcome = .returned 0 ∧
      nextPosition.input = [] ∧ nextPosition.output = cumulativeOutput numbers := by
  obtain ⟨modelSafe, finalRoom⟩ := validInput_safe_and_finalRoom valid
  have future := StreamFold.streamFuture_initial kernelSpec (0 : Float) position empty
    True.intro ((prefixFloats 0 numbers).map render) modelSafe finalRoom (model_completion valid)
  have shared := buffer_related.exec (a := initial) (b := StreamFold.initial (0 : Float))
    buffer_initial.symm execution
  obtain ⟨nextPosition, nextRep, returned, input, output⟩ :=
    StreamFold.process_exec_correct kernelSpec streams shared represented future
  exact ⟨nextPosition, nextRep, returned, input, output.trans (outputWords_fp numbers)⟩

theorem process_terminates_fp {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world : World} (represented : rep position world)
    (empty : position.output = []) (numbers : List Num) (valid : ValidInput position.input numbers) :
    ∃ trace final nextPosition, Process.Exec host process initial world trace (.returned 0) final ∧
      rep nextPosition final ∧ nextPosition.input = [] ∧
      nextPosition.output = cumulativeOutput numbers := by
  obtain ⟨modelSafe, finalRoom⟩ := validInput_safe_and_finalRoom valid
  obtain ⟨trace, final, nextPosition, shared, nextRep, input, output⟩ :=
    StreamFold.initial_terminates_output kernelSpec streams (0 : Float) represented empty
      True.intro ((prefixFloats 0 numbers).map render) modelSafe finalRoom (model_completion valid)
  exact ⟨trace, final, nextPosition, buffer_related.exec_back buffer_initial.symm shared,
    nextRep, input, output.trans (outputWords_fp numbers)⟩

def CommandFPResult {World : Type} (host : Host World)
    (rep : StreamPosition → World → Prop) (numbers : List Num)
    (outcome : Outcome Unit) (final : Observed World) : Prop :=
  stdoutWords final.events = cumulativeOutput numbers ∧
    ∃ before position, observedStreamRep rep position before ∧
      position.output = cumulativeOutput numbers ∧
      ((outcome = .exited 0 ∧ (observedHost host).exit before 0 final) ∨
        ∃ message, outcome = .trapped message ∧ (observedHost host).exitTrap before 0 message final)

theorem command_fp {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : Observed World} {trace : List Event}
    {outcome : Outcome Unit} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (numbers : List Num) (valid : ValidInput position.input numbers)
    (execution : ProcessCommandExec (observedHost host) begin process world trace outcome final) :
    CommandFPResult host rep numbers outcome final := by
  have observed : observedStreamRep rep position world :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  cases execution with
  | next started continued finished =>
      change LeanExe.Wasi.Exec (observedHost host) (.pure (⟨true, 0, initial⟩ : ProcessStep State))
        _ _ _ _ at started
      cases started
      change Process.Exec (observedHost host) process initial _ _ _ _ at continued
      obtain ⟨nextPosition, nextRep, returned, _, output⟩ :=
        process_fp_correct streams.observed observed empty numbers valid continued
      cases returned
      change LeanExe.Wasi.Exec (observedHost host) (Action.exit (α := Unit) 0)
        _ _ _ _ at finished
      cases finished with
      | exit accepted =>
          have finalOutput := Demos.RunningSum.observedStreamRep_exit_output nextRep accepted
          exact ⟨finalOutput.symm.trans output, _, nextPosition, nextRep, output, Or.inl ⟨rfl, accepted⟩⟩
      | exitTrap rejected =>
          have finalOutput := Demos.RunningSum.observedStreamRep_exitTrap_output nextRep rejected
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
