import Demos.StreamFold.FutureBase
import Demos.StreamFold.Host

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

variable {Acc : Type} {kernel : Kernel Acc} (spec : KernelSpec kernel)

theorem streamFuture_consumeInput {state : BufferState Acc} {position : StreamPosition}
    {history expected : List Bytes} {status : UInt64}
    (future : StreamFuture spec state position history expected status)
    (finished : ¬ state.written < state.output.size) :
    ((consumeInput kernel state).running = true → (consumeInput kernel state).status = 0 ∧
      StreamFuture spec (consumeInput kernel state).state position
        (history ++ bufferOutputs (consumeInput kernel state).state) expected status) ∧
    ((consumeInput kernel state).running = false →
      (consumeInput kernel state).status = status ∧ StreamDone position expected status) := by
  have noOutput := future.safe.no_output finished
  have empty : state.output.size = 0 := by simp [Bytes.size, noOutput.1]
  have modelSafe := (Model.safe_append_iff spec _ (unreadWords state) position.input).mp
    future.modelSafe
  obtain ⟨consumed, progress⟩ := consumeInput_buffer spec state history future.safe empty
    future.normal modelSafe.1
  have split : remainingInput state position =
      consumed ++ remainingInput (consumeInput kernel state).state position := by
    change unreadWords state ++ position.input = _
    rw [progress.split, List.append_assoc]
    rfl
  refine ⟨fun running => ?_, fun stopped => ?_⟩
  · obtain ⟨status, normal, executed⟩ := progress.running running
    refine ⟨status, ?_⟩
    apply StreamFuture.of_consumed spec future _ progress.safe normal
    · intro eof
      rw [progress.input]
      exact future.eof_buffer (progress.eof ▸ eof)
    · intro eof
      exact future.eof_input (progress.eof ▸ eof)
    · simp only [outputWords, List.flatMap_append]
      change outputWords history ++ outputWords (bufferOutputs (consumeInput kernel state).state) = _
      rw [future.output, remainingOutput_empty future.safe empty, List.append_nil,
        outputWords_bufferOutputs, remainingOutput_words_safe progress.safe,
        consumeInput_written_zero state noOutput.2, UInt64.toNat_zero, List.drop_zero]
    · exact split
    · exact executed
  · obtain ⟨rejected, executed⟩ := progress.stopped stopped
    have completed := future.completion
    rw [split, Model.outcome_append_error _ executed] at completed
    obtain ⟨expectedEq, statusEq⟩ := Prod.mk.inj completed
    subst expectedEq statusEq
    refine ⟨rejected, ?_, fun zero => absurd zero (by decide)⟩
    simpa only [bufferModel, remainingOutput_empty future.safe empty, List.append_nil] using
      future.output.symm

theorem streamFuture_writeStep {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {state : (BufferState Acc)} {position : StreamPosition}
    {history expected : List Bytes} {status : UInt64} {world final : World} {trace : List Event}
    {next : ProcessStep (BufferState Acc)} (represented : rep position world)
    (future : StreamFuture spec state position history expected status)
    (pending : state.written < state.output.size)
    (execution : LeanExe.Wasi.Exec host (writeStep state) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧ next.running = true ∧ next.status = 0 ∧
      StreamFuture spec next.state nextPosition history expected status := by
  change LeanExe.Wasi.Exec host
    (.write .stdout (remainingOutput state) fun reply => .pure (afterWrite state reply))
    world trace (.returned next) final at execution
  cases execution with
  | write_return operation continuation =>
      cases continuation
      obtain ⟨count, nextPosition, replyEq, nextRep, input, output, _⟩ :=
        streams.write_reply represented (remainingOutput_nonempty future.safe pending)
          operation
      cases replyEq
      simp only [writeResult, ↓reduceIte]
      have bound := (host.write_bound operation).1
      refine ⟨nextPosition, nextRep, ?_, ?_, streamFuture_afterWrite spec future _ bound input output⟩
      · simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        split <;> rfl
      · simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        split <;> rfl

theorem streamFuture_readStep {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {state : (BufferState Acc)} {position : StreamPosition}
    {history expected : List Bytes} {status : UInt64} {world final : World} {trace : List Event}
    {next : ProcessStep (BufferState Acc)} (represented : rep position world)
    (future : StreamFuture spec state position history expected status)
    (exhausted : ¬ state.cursor < state.input.size)
    (execution : LeanExe.Wasi.Exec host (readStep state) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧ next.running = true ∧ next.status = 0 ∧
      StreamFuture spec next.state nextPosition history expected status := by
  change LeanExe.Wasi.Exec host (.read 4096 fun reply => .pure (afterRead state reply))
    world trace (.returned next) final at execution
  cases execution with
  | read_reject capacity continuation =>
      exact False.elim ((by decide : ¬ 2 ^ 32 ≤ (4096 : UInt64).toNat) capacity)
  | read_return capacity operation continuation =>
      cases continuation
      obtain ⟨bytes, nextPosition, replyEq, nextRep, input, eof, output⟩ :=
        streams.read_reply represented operation
      cases replyEq
      simp only [readResult, ↓reduceIte]
      exact ⟨nextPosition, nextRep, by simp [afterRead], by simp [afterRead],
        streamFuture_afterRead spec future _ (host.read_bound operation).1 exhausted input eof output⟩

theorem streamFuture_empty_line {state : BufferState Acc} {position : StreamPosition}
    {history expected : List Bytes} {status : UInt64}
    (future : StreamFuture spec state position history expected status)
    (eof : state.eof = true) (empty : state.line.size.toUInt64 = 0) : state.line.size = 0 := by
  by_cases lineEmpty : state.line.size = 0
  · exact lineEmpty
  · have room := StreamFuture.eof_room spec future eof lineEmpty
    have lineBound : state.line.size < UInt64.size := spec.lineFits room
    have sizeNat := UInt64.toNat_ofNat_of_lt' lineBound
    have zeroNat := congrArg UInt64.toNat empty
    simpa only [sizeNat, UInt64.toNat_zero] using zeroNat

theorem streamFuture_terminal {state : BufferState Acc} {position : StreamPosition}
    {history expected : List Bytes} {status : UInt64}
    (future : StreamFuture spec state position history expected status)
    (finished : ¬ state.written < state.output.size) (eof : state.eof = true)
    (empty : state.line.size.toUInt64 = 0) : 0 = status ∧ StreamDone position expected status := by
  have lineEmpty := streamFuture_empty_line spec future eof empty
  have completed := future.completion
  rw [StreamFuture.eof_remaining spec future eof] at completed
  have finishEq : Model.finish kernel (bufferModel state history) = .ok (bufferModel state history) := by
    simp [Model.finish, bufferModel, lineEmpty]
  simp only [Model.outcome, Model.consume_nil, bind, Except.bind, finishEq, Prod.mk.injEq] at completed
  obtain ⟨historyEq, statusEq⟩ := completed
  subst statusEq
  have noOutput := future.safe.no_output finished
  have outputEmpty : state.output.size = 0 := by simp [Bytes.size, noOutput.1]
  refine ⟨rfl, ?_, fun _ => future.eof_input eof⟩
  rw [← historyEq]
  simpa only [bufferModel, remainingOutput_empty future.safe outputEmpty, List.append_nil] using
    future.output.symm

theorem streamFuture_completeLine {state : BufferState Acc} {position : StreamPosition}
    {history expected : List Bytes} {status : UInt64}
    (future : StreamFuture spec state position history expected status)
    (finished : ¬ state.written < state.output.size) (eof : state.eof = true)
    (nonempty : state.line.size.toUInt64 ≠ 0) :
    ((completeLine kernel state).running = true → (completeLine kernel state).status = 0 ∧
      StreamFuture spec (completeLine kernel state).state position
        (history ++ [(completeLine kernel state).state.output]) expected status) ∧
    ((completeLine kernel state).running = false →
      (completeLine kernel state).status = status ∧ StreamDone position expected status) := by
  have lineNonempty : state.line.size ≠ 0 := by
    intro empty
    exact nonempty (by simp [empty])
  have remaining := StreamFuture.eof_remaining spec future eof
  have completed := future.completion
  rw [remaining] at completed
  have noOutput := future.safe.no_output finished
  have empty : state.output.size = 0 := by simp [Bytes.size, noOutput.1]
  cases accepted : (kernel state.total state.line).valid with
  | false =>
      have stoppedEq : completeLine kernel state = ⟨false, 28, state⟩ := by
        simp [completeLine, accepted]
      simp only [Model.outcome, Model.consume_nil, bind, Except.bind, Model.finish, bufferModel,
        lineNonempty, ↓reduceIte, Model.emitLine, accepted, Bool.false_eq_true,
        Prod.mk.injEq] at completed
      obtain ⟨historyEq, statusEq⟩ := completed
      subst historyEq statusEq
      rw [stoppedEq]
      refine ⟨fun running => (nomatch running), fun _ => ⟨rfl, ?_, fun zero => absurd zero (by decide)⟩⟩
      simpa only [remainingOutput_empty future.safe empty, List.append_nil] using
        future.output.symm
  | true =>
      have room := StreamFuture.eof_room spec future eof lineNonempty
      have facts := completeLine_buffer spec state history future.normal room accepted
      have finishExec : Model.finish kernel (bufferModel state history) =
          .ok (bufferModel (completeLine kernel state).state
            (history ++ [(completeLine kernel state).state.output])) := by
        simpa only [Model.finish, bufferModel, lineNonempty, ↓reduceIte,
          Model.consumeByte, beq_self_eq_true] using facts.2.2.2.2
      have nextSafe := completeLine_safe spec future.safe
      have clearLine : (completeLine kernel state).state.line = #[] := by
        simp [completeLine, accepted]
      have zeroWritten : (completeLine kernel state).state.written = 0 := by
        simp [completeLine, accepted]
      have nextRemaining : remainingInput (completeLine kernel state).state position = [] := by
        simp [remainingInput, unreadWords, completeLine_input,
          byteWords_nil state.input (future.eof_buffer eof), future.eof_input eof]
      have nextFinish : Model.finish kernel (bufferModel (completeLine kernel state).state
          (history ++ [(completeLine kernel state).state.output])) =
          .ok (bufferModel (completeLine kernel state).state
            (history ++ [(completeLine kernel state).state.output])) := by
        simp [Model.finish, bufferModel, clearLine]
      refine ⟨fun _ => ⟨facts.2.1, nextSafe, facts.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun stopped => ?_⟩
      · intro _
        rw [completeLine_input]
        exact future.eof_buffer eof
      · intro _
        exact future.eof_input eof
      · simp only [outputWords, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
        change outputWords history ++ byteWords (completeLine kernel state).state.output = _
        rw [future.output, remainingOutput_empty future.safe empty, List.append_nil,
          remainingOutput_words_safe nextSafe, zeroWritten, UInt64.toNat_zero, List.drop_zero]
      · simp only [nextRemaining, Model.Safe]
      · intro ending executed endingNonempty
        have endingEq : ending = bufferModel (completeLine kernel state).state
            (history ++ [(completeLine kernel state).state.output]) := by
          simpa only [nextRemaining, Model.consume_nil, Except.ok.injEq] using executed.symm
        have emptyPending : ending.pending.size = 0 := by simp [endingEq, bufferModel, clearLine]
        exact False.elim (endingNonempty emptyPending)
      · rw [nextRemaining, ← completed]
        simp only [Model.outcome, Model.consume_nil, bind, Except.bind, nextFinish, finishExec]
      · rw [facts.1] at stopped
        cases stopped

theorem streamFuture_step {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {state : BufferState Acc} {position : StreamPosition}
    {history expected : List Bytes} {status : UInt64} {world final : World} {trace : List Event}
    {next : ProcessStep (BufferState Acc)} (represented : rep position world)
    (future : StreamFuture spec state position history expected status)
    (execution : LeanExe.Wasi.Exec host (step kernel state) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧
      (next.running = true →
        ∃ history', StreamFuture spec next.state nextPosition history' expected status) ∧
      (next.running = false → next.status = status ∧ StreamDone nextPosition expected status) := by
  by_cases pending : state.written < state.output.size
  · have code : step kernel state = writeStep state := by simp [step, pending]
    rw [code] at execution
    obtain ⟨nextPosition, nextRep, running, _, preserved⟩ :=
      streamFuture_writeStep spec streams represented future pending execution
    refine ⟨nextPosition, nextRep, fun _ => ⟨history, preserved⟩, ?_⟩
    intro stopped
    rw [running] at stopped
    cases stopped
  · by_cases remaining : state.cursor < state.input.size
    · have code : step kernel state = .pure (consumeInput kernel state) := by
        simp [step, pending, remaining]
        rfl
      rw [code] at execution
      cases execution
      obtain ⟨continued, stopped⟩ := streamFuture_consumeInput spec future pending
      exact ⟨position, represented, fun running => ⟨_, (continued running).2⟩, stopped⟩
    · cases eof : state.eof with
      | false =>
          have code : step kernel state = readStep state := by simp [step, pending, remaining, eof]
          rw [code] at execution
          obtain ⟨nextPosition, nextRep, running, _, preserved⟩ :=
            streamFuture_readStep spec streams represented future remaining execution
          refine ⟨nextPosition, nextRep, fun _ => ⟨history, preserved⟩, ?_⟩
          intro stopped
          rw [running] at stopped
          cases stopped
      | true =>
          by_cases empty : state.line.size.toUInt64 = 0
          · have code : step kernel state = .pure ⟨false, 0, state⟩ := by
              simp [step, pending, remaining, eof, empty]
              rfl
            rw [code] at execution
            cases execution
            refine ⟨position, represented, ?_, ?_⟩
            · intro impossible
              cases impossible
            · intro _
              exact streamFuture_terminal spec future pending eof empty
          · have code : step kernel state = .pure (completeLine kernel state) := by
              simp [step, pending, remaining, eof, empty]
              rfl
            rw [code] at execution
            cases execution
            obtain ⟨continued, stopped⟩ := streamFuture_completeLine spec future pending eof empty
            exact ⟨position, represented, fun running => ⟨_, (continued running).2⟩, stopped⟩

end Demos.StreamFold
