import Demos.RunningSum.StreamFutureSteps
import Demos.RunningSum.StreamObserved
import Verified.Wasi.ProcessEntryProofs

namespace Demos.RunningSum

open LeanExe LeanExe.Wasi Verified.Wasi

def integerWords (value : Int) : List UInt64 := (integerEncoding value).map UInt8.toUInt64

def cumulativeOutput (inputs : List (Array UInt64)) : List UInt64 :=
  (StreamModel.prefixSums 0 inputs).flatMap integerWords

theorem outputWords_correct {values : List Int} {output : List Bytes}
    (encoded : List.Forall₂ DecimalOutput values output) :
    outputWords output = values.flatMap integerWords := by
  induction encoded with
  | nil => rfl
  | cons same rest ih =>
      change byteWords _ ++ outputWords _ = integerWords _ ++ _
      rw [ih]
      unfold byteWords integerWords
      rw [same]
      rfl

theorem process_exec_correct {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {state : State} {world final : World} {trace : List Event} {outcome : Outcome UInt64}
    (execution : Process.Exec host process state world trace outcome final)
    {position : StreamPosition} {history expected : List Bytes}
    (represented : rep position world) (future : StreamFuture state position history expected) :
    ∃ nextPosition, rep nextPosition final ∧ outcome = .returned 0 ∧
      nextPosition.input = [] ∧ nextPosition.output = outputWords expected := by
  induction execution generalizing position history with
  | done execution stopped =>
      obtain ⟨nextPosition, nextRep, _, finished⟩ :=
        streamFuture_step streams represented future execution
      obtain ⟨status, input, output⟩ := finished stopped
      exact ⟨nextPosition, nextRep, congrArg Outcome.returned status, input, output⟩
  | next execution running continuation ih =>
      obtain ⟨nextPosition, nextRep, continued, _⟩ :=
        streamFuture_step streams represented future execution
      obtain ⟨nextHistory, nextFuture⟩ := continued running
      exact ih nextRep nextFuture
  | exit execution =>
      obtain ⟨next, impossible⟩ :=
        Termination.step_returned streams.progress represented future.safe execution
      cases impossible
  | trap execution =>
      obtain ⟨next, impossible⟩ :=
        Termination.step_returned streams.progress represented future.safe execution
      cases impossible

theorem process_exec_integer {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : World} {trace : List Event}
    {outcome : Outcome UInt64} (represented : rep position world) (empty : position.output = [])
    (inputs : List (Array UInt64)) (valid : StreamModel.ValidInput position.input inputs)
    (bounds : StreamModel.InputBounds inputs)
    (execution : Process.Exec host process initial world trace outcome final) :
    ∃ nextPosition, rep nextPosition final ∧ outcome = .returned 0 ∧
      nextPosition.input = [] ∧ nextPosition.output = cumulativeOutput inputs := by
  obtain ⟨expected, future, encoded⟩ := streamFuture_initial position empty inputs valid bounds
  obtain ⟨nextPosition, nextRep, returned, input, output⟩ :=
    process_exec_correct streams execution represented future
  exact ⟨nextPosition, nextRep, returned, input,
    output.trans (outputWords_correct encoded)⟩

theorem process_terminates_integer {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world : World} (represented : rep position world)
    (empty : position.output = []) (inputs : List (Array UInt64))
    (valid : StreamModel.ValidInput position.input inputs) (bounds : StreamModel.InputBounds inputs) :
    ∃ trace final nextPosition, Process.Exec host process initial world trace (.returned 0) final ∧
      rep nextPosition final ∧ nextPosition.input = [] ∧
      nextPosition.output = cumulativeOutput inputs := by
  obtain ⟨trace, status, final, _, execution, _, _⟩ :=
    Termination.initial_terminates streams.progress represented
  obtain ⟨nextPosition, nextRep, returned, input, output⟩ :=
    process_exec_integer streams represented empty inputs valid bounds execution
  cases returned
  exact ⟨trace, final, nextPosition, execution, nextRep, input, output⟩

def CommandIntegerResult {World : Type} (host : Host World)
    (rep : StreamPosition → World → Prop) (inputs : List (Array UInt64))
    (outcome : Outcome Unit) (final : Observed World) : Prop :=
  stdoutWords final.events = cumulativeOutput inputs ∧
    ∃ before position, observedStreamRep rep position before ∧
      position.output = cumulativeOutput inputs ∧
      ((outcome = .exited 0 ∧ (observedHost host).exit before 0 final) ∨
        ∃ message, outcome = .trapped message ∧ (observedHost host).exitTrap before 0 message final)

theorem command_integer {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : Observed World} {trace : List Event}
    {outcome : Outcome Unit} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (inputs : List (Array UInt64)) (valid : StreamModel.ValidInput position.input inputs)
    (bounds : StreamModel.InputBounds inputs)
    (execution : ProcessCommandExec (observedHost host) begin process world trace outcome final) :
    CommandIntegerResult host rep inputs outcome final := by
  have observed : observedStreamRep rep position world := by
    exact ⟨represented, by simp [empty, events, stdoutWords]⟩
  cases execution with
  | next started continued finished =>
      change LeanExe.Wasi.Exec (observedHost host) (.pure (⟨true, 0, initial⟩ : ProcessStep State))
        _ _ _ _ at started
      cases started
      change Process.Exec (observedHost host) process initial _ _ _ _ at continued
      obtain ⟨nextPosition, nextRep, returned, _, output⟩ :=
        process_exec_integer streams.observed observed empty inputs valid bounds continued
      cases returned
      change LeanExe.Wasi.Exec (observedHost host) (Action.exit (α := Unit) 0)
        _ _ _ _ at finished
      cases finished with
      | exit accepted =>
          have finalOutput := observedStreamRep_exit_output nextRep accepted
          exact ⟨finalOutput.symm.trans output, _, nextPosition, nextRep, output, Or.inl ⟨rfl, accepted⟩⟩
      | exitTrap rejected =>
          have finalOutput := observedStreamRep_exitTrap_output nextRep rejected
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
