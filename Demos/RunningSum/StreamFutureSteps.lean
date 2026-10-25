import Demos.RunningSum.StreamFutureStepsBase

namespace Demos.RunningSum

open LeanExe LeanExe.Wasi

theorem streamFuture_consumeInput {state : State} {position : StreamPosition}
    {history expected : List Bytes} (future : StreamFuture state position history expected)
    (finished : ¬ state.written < state.output.size) :
    (consumeInput state).running = true ∧ (consumeInput state).status = 0 ∧
      StreamFuture (consumeInput state).state position
        (history ++ bufferOutputs (consumeInput state).state) expected := by
  have noOutput := future.safe.no_output finished
  have empty : state.output.size = 0 := by simp [Bytes.size, noOutput.1]
  obtain ⟨processed, final, completed, _, _⟩ := future.completion
  obtain ⟨bufferFinal, consumed, remaining⟩ :=
    model_prefix_success (bufferModel state history) (unreadWords state) position.input processed
      completed
  have modelSafe := (StreamModel.safe_append_iff _ (unreadWords state) position.input).mp
    future.modelSafe
  have progress := consumeInput_buffer state history bufferFinal future.safe empty future.normal
    modelSafe.1 consumed
  refine ⟨progress.running, progress.status, ?_⟩
  apply future.of_consumed _ progress.safe progress.normal
  · intro eof
    rw [progress.input]
    exact future.eof_buffer (progress.eof ▸ eof)
  · intro eof
    exact future.eof_input (progress.eof ▸ eof)
  · simp only [outputWords, List.flatMap_append]
    change outputWords history ++ outputWords (bufferOutputs (consumeInput state).state) = _
    rw [future.output, remainingOutput_empty future.safe empty, List.append_nil,
      outputWords_bufferOutputs, remainingOutput_words_safe progress.safe,
      consumeInput_written_zero state noOutput.2, UInt64.toNat_zero, List.drop_zero]
  · change unreadWords state ++ position.input = _
    conv_lhs => rw [progress.split]
    exact List.append_assoc _ _ _
  · exact progress.consumed

theorem streamFuture_writeStep {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {state : State} {position : StreamPosition}
    {history expected : List Bytes} {world final : World} {trace : List Event}
    {next : ProcessStep State} (represented : rep position world)
    (future : StreamFuture state position history expected)
    (pending : state.written < state.output.size)
    (execution : LeanExe.Wasi.Exec host (writeStep state) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧ next.running = true ∧ next.status = 0 ∧
      StreamFuture next.state nextPosition history expected := by
  change LeanExe.Wasi.Exec host
    (.write .stdout (remainingOutput state) fun reply => .pure (afterWrite state reply))
    world trace (.returned next) final at execution
  cases execution with
  | write_return operation continuation =>
      cases continuation
      obtain ⟨count, nextPosition, replyEq, nextRep, input, output, _⟩ :=
        streams.write_reply represented (Termination.remainingOutput_nonempty future.safe pending)
          operation
      cases replyEq
      simp only [writeResult, ↓reduceIte]
      have bound := (host.write_bound operation).1
      refine ⟨nextPosition, nextRep, ?_, ?_, streamFuture_afterWrite future _ bound input output⟩
      · simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        split <;> rfl
      · simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        split <;> rfl

theorem streamFuture_readStep {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {state : State} {position : StreamPosition}
    {history expected : List Bytes} {world final : World} {trace : List Event}
    {next : ProcessStep State} (represented : rep position world)
    (future : StreamFuture state position history expected)
    (exhausted : ¬ state.cursor < state.input.size)
    (execution : LeanExe.Wasi.Exec host (readStep state) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧ next.running = true ∧ next.status = 0 ∧
      StreamFuture next.state nextPosition history expected := by
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
        streamFuture_afterRead future _ (host.read_bound operation).1 exhausted input eof output⟩

theorem streamFuture_empty_line {state : State} {position : StreamPosition}
    {history expected : List Bytes} (future : StreamFuture state position history expected)
    (eof : state.eof = true) (empty : state.line.size.toUInt64 = 0) : state.line.size = 0 := by
  by_cases lineEmpty : state.line.size = 0
  · exact lineEmpty
  · have room := future.eof_room eof lineEmpty
    change max state.total.digits.size state.line.size + 3 < UInt64.size at room
    have lineBound : state.line.size < UInt64.size := by omega
    have sizeNat := UInt64.toNat_ofNat_of_lt' lineBound
    have zeroNat := congrArg UInt64.toNat empty
    simpa only [sizeNat, UInt64.toNat_zero] using zeroNat

theorem streamFuture_terminal {state : State} {position : StreamPosition}
    {history expected : List Bytes} (future : StreamFuture state position history expected)
    (finished : ¬ state.written < state.output.size) (eof : state.eof = true)
    (empty : state.line.size.toUInt64 = 0) :
    position.input = [] ∧ position.output = outputWords expected := by
  have lineEmpty := streamFuture_empty_line future eof empty
  have remaining := future.eof_remaining eof
  obtain ⟨processed, final, completed, finishedModel, output⟩ := future.completion
  have processedEq : processed = bufferModel state history := by
    simpa only [remaining, StreamModel.consume_nil, Except.ok.injEq] using completed.symm
  have finalEq : final = bufferModel state history := by
    simpa [processedEq, StreamModel.finish, bufferModel, lineEmpty] using finishedModel.symm
  have historyEq : history = expected := by simpa only [finalEq, bufferModel] using output
  have noOutput := future.safe.no_output finished
  have outputEmpty : state.output.size = 0 := by simp [Bytes.size, noOutput.1]
  refine ⟨future.eof_input eof, ?_⟩
  rw [← historyEq]
  simpa only [remainingOutput_empty future.safe outputEmpty, List.append_nil] using future.output.symm

theorem streamFuture_completeLine {state : State} {position : StreamPosition}
    {history expected : List Bytes} (future : StreamFuture state position history expected)
    (finished : ¬ state.written < state.output.size) (eof : state.eof = true)
    (nonempty : state.line.size.toUInt64 ≠ 0) :
    (completeLine state).running = true ∧ (completeLine state).status = 0 ∧
      StreamFuture (completeLine state).state position
        (history ++ [(completeLine state).state.output]) expected := by
  have lineNonempty : state.line.size ≠ 0 := by
    intro empty
    exact nonempty (by simp [empty])
  have remaining := future.eof_remaining eof
  have room := future.eof_room eof lineNonempty
  obtain ⟨processed, final, completed, finishedModel, output⟩ := future.completion
  have processedEq : processed = bufferModel state history := by
    simpa only [remaining, StreamModel.consume_nil, Except.ok.injEq] using completed.symm
  rw [processedEq] at finishedModel
  have accepted : (parse state.line).valid = true := by
    by_contra rejected
    have parseFalse : (parse state.line).valid = false := Bool.eq_false_iff.mpr rejected
    simp [StreamModel.finish, StreamModel.emitLine, bufferModel, lineNonempty, parseFalse]
      at finishedModel
  have facts := completeLine_buffer state history future.normal room accepted
  have finishExec : StreamModel.finish (bufferModel state history) =
      .ok (bufferModel (completeLine state).state
        (history ++ [(completeLine state).state.output])) := by
    simpa only [StreamModel.finish, bufferModel, lineNonempty, ↓reduceIte,
      StreamModel.consumeByte, beq_self_eq_true] using facts.2.2.2.2
  have finalEq := Except.ok.inj (finishedModel.symm.trans finishExec)
  have expectedEq : history ++ [(completeLine state).state.output] = expected := by
    simpa only [finalEq, bufferModel] using output
  have nextSafe := Termination.completeLine_safe future.safe
  have clearLine : (completeLine state).state.line = #[] := by simp [completeLine, accepted]
  have zeroWritten : (completeLine state).state.written = 0 := by simp [completeLine, accepted]
  have nextRemaining : remainingInput (completeLine state).state position = [] := by
    simp [remainingInput, unreadWords, Termination.completeLine_input,
      byteWords_nil state.input (future.eof_buffer eof), future.eof_input eof]
  have noOutput := future.safe.no_output finished
  have empty : state.output.size = 0 := by simp [Bytes.size, noOutput.1]
  refine ⟨facts.1, facts.2.1, nextSafe, facts.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    rw [Termination.completeLine_input]
    exact future.eof_buffer eof
  · intro _
    exact future.eof_input eof
  · simp only [outputWords, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    change outputWords history ++ byteWords (completeLine state).state.output = _
    rw [future.output, remainingOutput_empty future.safe empty, List.append_nil,
      remainingOutput_words_safe nextSafe, zeroWritten, UInt64.toNat_zero, List.drop_zero]
  · simp only [nextRemaining, StreamModel.Safe]
  · intro ending executed endingNonempty
    have endingEq : ending = bufferModel (completeLine state).state
        (history ++ [(completeLine state).state.output]) := by
      simpa only [nextRemaining, StreamModel.consume_nil, Except.ok.injEq] using executed.symm
    have emptyPending : ending.pending.size = 0 := by simp [endingEq, bufferModel, clearLine]
    exact False.elim (endingNonempty emptyPending)
  · refine ⟨bufferModel (completeLine state).state (history ++ [(completeLine state).state.output]),
      bufferModel (completeLine state).state (history ++ [(completeLine state).state.output]),
      ?_, ?_, expectedEq⟩
    · simp only [nextRemaining, StreamModel.consume_nil]
    · simp [StreamModel.finish, bufferModel, clearLine]

theorem streamFuture_step {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {state : State} {position : StreamPosition}
    {history expected : List Bytes} {world final : World} {trace : List Event}
    {next : ProcessStep State} (represented : rep position world)
    (future : StreamFuture state position history expected)
    (execution : LeanExe.Wasi.Exec host (step state) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧
      (next.running = true → ∃ history', StreamFuture next.state nextPosition history' expected) ∧
      (next.running = false → next.status = 0 ∧ nextPosition.input = [] ∧
        nextPosition.output = outputWords expected) := by
  by_cases pending : state.written < state.output.size
  · have code : step state = writeStep state := by simp [step, pending]
    rw [code] at execution
    obtain ⟨nextPosition, nextRep, running, _, preserved⟩ :=
      streamFuture_writeStep streams represented future pending execution
    refine ⟨nextPosition, nextRep, fun _ => ⟨history, preserved⟩, ?_⟩
    intro stopped
    rw [running] at stopped
    cases stopped
  · by_cases remaining : state.cursor < state.input.size
    · have code : step state = .pure (consumeInput state) := by
        simp [step, pending, remaining]
        rfl
      rw [code] at execution
      cases execution
      obtain ⟨running, _, preserved⟩ := streamFuture_consumeInput future pending
      refine ⟨position, represented, fun _ => ⟨_, preserved⟩, ?_⟩
      intro stopped
      rw [running] at stopped
      cases stopped
    · cases eof : state.eof with
      | false =>
          have code : step state = readStep state := by simp [step, pending, remaining, eof]
          rw [code] at execution
          obtain ⟨nextPosition, nextRep, running, _, preserved⟩ :=
            streamFuture_readStep streams represented future remaining execution
          refine ⟨nextPosition, nextRep, fun _ => ⟨history, preserved⟩, ?_⟩
          intro stopped
          rw [running] at stopped
          cases stopped
      | true =>
          by_cases empty : state.line.size.toUInt64 = 0
          · have code : step state = .pure ⟨false, 0, state⟩ := by
              simp [step, pending, remaining, eof, empty]
              rfl
            rw [code] at execution
            cases execution
            refine ⟨position, represented, ?_, ?_⟩
            · intro impossible
              cases impossible
            · intro _
              exact ⟨rfl, streamFuture_terminal future pending eof empty⟩
          · have code : step state = .pure (completeLine state) := by
              simp [step, pending, remaining, eof, empty]
              rfl
            rw [code] at execution
            cases execution
            obtain ⟨running, _, preserved⟩ := streamFuture_completeLine future pending eof empty
            refine ⟨position, represented, fun _ => ⟨_, preserved⟩, ?_⟩
            intro stopped
            rw [running] at stopped
            cases stopped

end Demos.RunningSum
