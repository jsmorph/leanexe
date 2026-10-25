import Demos.StreamFold.FutureBase
import Demos.StreamFold.Host

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

variable {Acc : Type} {kernel : Kernel Acc} (spec : KernelSpec kernel)

theorem streamFuture_consumeInput {state : (BufferState Acc)} {position : StreamPosition}
    {history expected : List Bytes} (future : StreamFuture spec state position history expected)
    (finished : ¬ state.written < state.output.size) :
    ((consumeInput kernel) state).running = true ∧ ((consumeInput kernel) state).status = 0 ∧
      StreamFuture spec ((consumeInput kernel) state).state position
        (history ++ bufferOutputs ((consumeInput kernel) state).state) expected := by
  have noOutput := future.safe.no_output finished
  have empty : state.output.size = 0 := by simp [Bytes.size, noOutput.1]
  obtain ⟨processed, final, completed, _, _⟩ := future.completion
  obtain ⟨bufferFinal, consumed, remaining⟩ :=
    model_prefix_success (bufferModel state history) (unreadWords state) position.input processed
      completed
  have modelSafe := (Model.safe_append_iff spec _ (unreadWords state) position.input).mp
    future.modelSafe
  have progress := consumeInput_buffer spec state history bufferFinal future.safe empty future.normal
    modelSafe.1 consumed
  refine ⟨progress.running, progress.status, ?_⟩
  apply StreamFuture.of_consumed spec future _ progress.safe progress.normal
  · intro eof
    rw [progress.input]
    exact future.eof_buffer (progress.eof ▸ eof)
  · intro eof
    exact future.eof_input (progress.eof ▸ eof)
  · simp only [outputWords, List.flatMap_append]
    change outputWords history ++ outputWords (bufferOutputs ((consumeInput kernel) state).state) = _
    rw [future.output, remainingOutput_empty future.safe empty, List.append_nil,
      outputWords_bufferOutputs, remainingOutput_words_safe progress.safe,
      consumeInput_written_zero state noOutput.2, UInt64.toNat_zero, List.drop_zero]
  · change unreadWords state ++ position.input = _
    conv_lhs => rw [progress.split]
    exact List.append_assoc _ _ _
  · exact progress.consumed

theorem streamFuture_writeStep {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {state : (BufferState Acc)} {position : StreamPosition}
    {history expected : List Bytes} {world final : World} {trace : List Event}
    {next : ProcessStep (BufferState Acc)} (represented : rep position world)
    (future : StreamFuture spec state position history expected)
    (pending : state.written < state.output.size)
    (execution : LeanExe.Wasi.Exec host (writeStep state) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧ next.running = true ∧ next.status = 0 ∧
      StreamFuture spec next.state nextPosition history expected := by
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
    {history expected : List Bytes} {world final : World} {trace : List Event}
    {next : ProcessStep (BufferState Acc)} (represented : rep position world)
    (future : StreamFuture spec state position history expected)
    (exhausted : ¬ state.cursor < state.input.size)
    (execution : LeanExe.Wasi.Exec host (readStep state) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧ next.running = true ∧ next.status = 0 ∧
      StreamFuture spec next.state nextPosition history expected := by
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

theorem streamFuture_empty_line {state : (BufferState Acc)} {position : StreamPosition}
    {history expected : List Bytes} (future : StreamFuture spec state position history expected)
    (eof : state.eof = true) (empty : state.line.size.toUInt64 = 0) : state.line.size = 0 := by
  by_cases lineEmpty : state.line.size = 0
  · exact lineEmpty
  · have room := StreamFuture.eof_room spec future eof lineEmpty
    have lineBound : state.line.size < UInt64.size := spec.lineFits room
    have sizeNat := UInt64.toNat_ofNat_of_lt' lineBound
    have zeroNat := congrArg UInt64.toNat empty
    simpa only [sizeNat, UInt64.toNat_zero] using zeroNat

theorem streamFuture_terminal {state : (BufferState Acc)} {position : StreamPosition}
    {history expected : List Bytes} (future : StreamFuture spec state position history expected)
    (finished : ¬ state.written < state.output.size) (eof : state.eof = true)
    (empty : state.line.size.toUInt64 = 0) :
    position.input = [] ∧ position.output = outputWords expected := by
  have lineEmpty := streamFuture_empty_line spec future eof empty
  have remaining := StreamFuture.eof_remaining spec future eof
  obtain ⟨processed, final, completed, finishedModel, output⟩ := future.completion
  have processedEq : processed = bufferModel state history := by
    simpa only [remaining, Model.consume_nil, Except.ok.injEq] using completed.symm
  have finalEq : final = bufferModel state history := by
    simpa [processedEq, Model.finish, bufferModel, lineEmpty] using finishedModel.symm
  have historyEq : history = expected := by simpa only [finalEq, bufferModel] using output
  have noOutput := future.safe.no_output finished
  have outputEmpty : state.output.size = 0 := by simp [Bytes.size, noOutput.1]
  refine ⟨future.eof_input eof, ?_⟩
  rw [← historyEq]
  simpa only [remainingOutput_empty future.safe outputEmpty, List.append_nil] using future.output.symm

theorem streamFuture_completeLine {state : (BufferState Acc)} {position : StreamPosition}
    {history expected : List Bytes} (future : StreamFuture spec state position history expected)
    (finished : ¬ state.written < state.output.size) (eof : state.eof = true)
    (nonempty : state.line.size.toUInt64 ≠ 0) :
    ((completeLine kernel) state).running = true ∧ ((completeLine kernel) state).status = 0 ∧
      StreamFuture spec ((completeLine kernel) state).state position
        (history ++ [((completeLine kernel) state).state.output]) expected := by
  have lineNonempty : state.line.size ≠ 0 := by
    intro empty
    exact nonempty (by simp [empty])
  have remaining := StreamFuture.eof_remaining spec future eof
  have room := StreamFuture.eof_room spec future eof lineNonempty
  obtain ⟨processed, final, completed, finishedModel, output⟩ := future.completion
  have processedEq : processed = bufferModel state history := by
    simpa only [remaining, Model.consume_nil, Except.ok.injEq] using completed.symm
  rw [processedEq] at finishedModel
  have accepted : (kernel state.total state.line).valid = true := by
    by_contra rejected
    have parseFalse : (kernel state.total state.line).valid = false := Bool.eq_false_iff.mpr rejected
    simp [Model.finish, Model.emitLine, bufferModel, lineNonempty, parseFalse]
      at finishedModel
  have facts := completeLine_buffer spec state history future.normal room accepted
  have finishExec : Model.finish kernel (bufferModel state history) =
      .ok (bufferModel ((completeLine kernel) state).state
        (history ++ [((completeLine kernel) state).state.output])) := by
    simpa only [Model.finish, bufferModel, lineNonempty, ↓reduceIte,
      Model.consumeByte, beq_self_eq_true] using facts.2.2.2.2
  have finalEq := Except.ok.inj (finishedModel.symm.trans finishExec)
  have expectedEq : history ++ [((completeLine kernel) state).state.output] = expected := by
    simpa only [finalEq, bufferModel] using output
  have nextSafe := completeLine_safe spec future.safe
  have clearLine : (completeLine kernel state).state.line = #[] := by simp [completeLine, accepted]
  have zeroWritten : (completeLine kernel state).state.written = 0 := by simp [completeLine, accepted]
  have nextRemaining : remainingInput ((completeLine kernel) state).state position = [] := by
    simp [remainingInput, unreadWords, completeLine_input,
      byteWords_nil state.input (future.eof_buffer eof), future.eof_input eof]
  have noOutput := future.safe.no_output finished
  have empty : state.output.size = 0 := by simp [Bytes.size, noOutput.1]
  refine ⟨facts.1, facts.2.1, nextSafe, facts.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    rw [completeLine_input]
    exact future.eof_buffer eof
  · intro _
    exact future.eof_input eof
  · simp only [outputWords, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    change outputWords history ++ byteWords ((completeLine kernel) state).state.output = _
    rw [future.output, remainingOutput_empty future.safe empty, List.append_nil,
      remainingOutput_words_safe nextSafe, zeroWritten, UInt64.toNat_zero, List.drop_zero]
  · simp only [nextRemaining, Model.Safe]
  · intro ending executed endingNonempty
    have endingEq : ending = bufferModel ((completeLine kernel) state).state
        (history ++ [((completeLine kernel) state).state.output]) := by
      simpa only [nextRemaining, Model.consume_nil, Except.ok.injEq] using executed.symm
    have emptyPending : ending.pending.size = 0 := by simp [endingEq, bufferModel, clearLine]
    exact False.elim (endingNonempty emptyPending)
  · refine ⟨bufferModel ((completeLine kernel) state).state (history ++ [((completeLine kernel) state).state.output]),
      bufferModel ((completeLine kernel) state).state (history ++ [((completeLine kernel) state).state.output]),
      ?_, ?_, expectedEq⟩
    · simp only [nextRemaining, Model.consume_nil]
    · simp [Model.finish, bufferModel, clearLine]

theorem streamFuture_step {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {state : (BufferState Acc)} {position : StreamPosition}
    {history expected : List Bytes} {world final : World} {trace : List Event}
    {next : ProcessStep (BufferState Acc)} (represented : rep position world)
    (future : StreamFuture spec state position history expected)
    (execution : LeanExe.Wasi.Exec host ((step kernel) state) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧
      (next.running = true → ∃ history', StreamFuture spec next.state nextPosition history' expected) ∧
      (next.running = false → next.status = 0 ∧ nextPosition.input = [] ∧
        nextPosition.output = outputWords expected) := by
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
    · have code : (step kernel) state = .pure ((consumeInput kernel) state) := by
        simp [step, pending, remaining]
        rfl
      rw [code] at execution
      cases execution
      obtain ⟨running, _, preserved⟩ := streamFuture_consumeInput spec future pending
      refine ⟨position, represented, fun _ => ⟨_, preserved⟩, ?_⟩
      intro stopped
      rw [running] at stopped
      cases stopped
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
          · have code : (step kernel) state = .pure ⟨false, 0, state⟩ := by
              simp [step, pending, remaining, eof, empty]
              rfl
            rw [code] at execution
            cases execution
            refine ⟨position, represented, ?_, ?_⟩
            · intro impossible
              cases impossible
            · intro _
              exact ⟨rfl, streamFuture_terminal spec future pending eof empty⟩
          · have code : (step kernel) state = .pure ((completeLine kernel) state) := by
              simp [step, pending, remaining, eof, empty]
              rfl
            rw [code] at execution
            cases execution
            obtain ⟨running, _, preserved⟩ := streamFuture_completeLine spec future pending eof empty
            refine ⟨position, represented, fun _ => ⟨_, preserved⟩, ?_⟩
            intro stopped
            rw [running] at stopped
            cases stopped

end Demos.StreamFold

