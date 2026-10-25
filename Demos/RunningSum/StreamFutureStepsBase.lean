import Demos.RunningSum.StreamInvariant

namespace Demos.RunningSum

open LeanExe LeanExe.Wasi

theorem unreadWords_empty {state : State} (safe : Termination.Safe state)
    (exhausted : ¬ state.cursor < state.input.size) : unreadWords state = [] := by
  apply List.drop_eq_nil_of_le
  simp only [byteWords_length]
  have limit := UInt64.not_lt.mp exhausted
  have bound := UInt64.le_iff_toNat_le.mp limit
  simpa only [safe.input_toNat] using bound

theorem model_prefix_success (state : StreamModel.State) (a b : List UInt64)
    (final : StreamModel.State) (success : StreamModel.consume state (a ++ b) = .ok final) :
    ∃ middle, StreamModel.consume state a = .ok middle ∧
      StreamModel.consume middle b = .ok final := by
  rw [StreamModel.consume_append] at success
  cases first : StreamModel.consume state a with
  | error code => simp [first, bind, Except.bind] at success
  | ok middle => exact ⟨middle, rfl, by simpa [first, bind, Except.bind] using success⟩

theorem StreamFuture.of_consumed {state next : State} {position nextPosition : StreamPosition}
    {history nextHistory expected : List Bytes} (future : StreamFuture state position history expected)
    (consumed : List UInt64) (safe : Termination.Safe next) (normal : next.total.Valid)
    (eofBuffer : next.eof = true → next.input.data.size = 0)
    (eofInput : next.eof = true → nextPosition.input = [])
    (output : outputWords nextHistory = nextPosition.output ++ byteWords (remainingOutput next))
    (split : remainingInput state position = consumed ++ remainingInput next nextPosition)
    (executed : StreamModel.consume (bufferModel state history) consumed =
      .ok (bufferModel next nextHistory)) : StreamFuture next nextPosition nextHistory expected := by
  refine ⟨safe, normal, eofBuffer, eofInput, output, ?_, ?_, ?_⟩
  · have divided := (StreamModel.safe_append_iff _ consumed _).mp
      (show StreamModel.Safe (bufferModel state history)
        (consumed ++ remainingInput next nextPosition) from split ▸ future.modelSafe)
    exact divided.2 _ executed
  · intro final completed nonempty
    apply future.finalRoom final _ nonempty
    rw [split, StreamModel.consume_append, executed]
    simpa [bind, Except.bind] using completed
  · obtain ⟨processed, final, completed, finished, outputEq⟩ := future.completion
    rw [split, StreamModel.consume_append, executed] at completed
    exact ⟨processed, final, by simpa [bind, Except.bind] using completed, finished, outputEq⟩

theorem streamFuture_afterRead {state : State} {position nextPosition : StreamPosition}
    {history expected : List Bytes} (future : StreamFuture state position history expected)
    (bytes : Bytes) (bound : bytes.data.size ≤ (4096 : UInt64).toNat)
    (exhausted : ¬ state.cursor < state.input.size)
    (input : position.input = byteWords bytes ++ nextPosition.input)
    (eof : bytes.data.size = 0 → position.input = [])
    (output : nextPosition.output = position.output) :
    StreamFuture (afterRead state ⟨0, bytes⟩).state nextPosition history expected := by
  have sizeBound : bytes.data.size < UInt64.size := by
    have count : (4096 : UInt64).toNat = 4096 := rfl
    have size : UInt64.size = 18446744073709551616 := rfl
    omega
  have bytesNat := Bytes.size_toNat bytes sizeBound
  have bytesZero : bytes.size = 0 ↔ bytes.data.size = 0 := by
    constructor
    · intro empty
      have := congrArg UInt64.toNat empty
      simpa only [bytesNat, UInt64.toNat_zero] using this
    · intro empty
      simp [Bytes.size, empty]
  have remaining : remainingInput state position = position.input := by
    simp only [remainingInput, unreadWords_empty future.safe exhausted, List.nil_append]
  have nextRemaining : remainingInput (afterRead state ⟨0, bytes⟩).state nextPosition =
      byteWords bytes ++ nextPosition.input := by
    simp [remainingInput, unreadWords, afterRead]
  apply future.of_consumed [] (Termination.afterRead_safe future.safe bytes bound)
  · exact future.normal
  · intro atEof
    simpa only [afterRead, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      beq_iff_eq, bytesZero] using atEof
  · intro atEof
    have empty : bytes.data.size = 0 := by
      simpa only [afterRead, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        beq_iff_eq, bytesZero] using atEof
    have noInput := eof empty
    rw [noInput] at input
    exact (List.append_eq_nil_iff.mp input.symm).2
  · simpa only [afterRead, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      remainingOutput, output] using future.output
  · simpa only [List.nil_append, remaining, nextRemaining] using input
  · simp [afterRead, bufferModel]

theorem streamFuture_afterWrite {state : State} {position nextPosition : StreamPosition}
    {history expected : List Bytes} (future : StreamFuture state position history expected)
    (count : UInt64) (bound : count.toNat ≤ (remainingOutput state).data.size)
    (input : nextPosition.input = position.input)
    (output : nextPosition.output =
      position.output ++ (byteWords (remainingOutput state)).take count.toNat) :
    StreamFuture (afterWrite state ⟨0, count⟩).state nextPosition history expected := by
  have sameModel : bufferModel (afterWrite state ⟨0, count⟩).state history =
      bufferModel state history := by
    simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    split <;> rfl
  have sameInput : (afterWrite state ⟨0, count⟩).state.input = state.input := by
    simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    split <;> rfl
  have sameCursor : (afterWrite state ⟨0, count⟩).state.cursor = state.cursor := by
    simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    split <;> rfl
  have sameEof : (afterWrite state ⟨0, count⟩).state.eof = state.eof := by
    simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    split <;> rfl
  apply future.of_consumed [] (Termination.afterWrite_safe future.safe count bound)
  · change (bufferModel (afterWrite state ⟨0, count⟩).state history).total.Valid
    rw [sameModel]
    exact future.normal
  · intro atEof
    rw [sameInput]
    exact future.eof_buffer (sameEof ▸ atEof)
  · intro atEof
    rw [input]
    exact future.eof_input (sameEof ▸ atEof)
  · rw [output, afterWrite_conservation future.safe count bound, ← future.output]
  · simp only [remainingInput, unreadWords, sameInput, sameCursor, input, List.nil_append]
  · simp only [StreamModel.consume_nil, sameModel]

theorem byteWords_nil (bytes : Bytes) (empty : bytes.data.size = 0) : byteWords bytes = [] :=
  List.eq_nil_of_length_eq_zero (by simpa only [byteWords_length] using empty)

theorem remainingOutput_empty {state : State} (safe : Termination.Safe state)
    (empty : state.output.size = 0) : byteWords (remainingOutput state) = [] := by
  have emptyNat := congrArg UInt64.toNat empty
  rw [safe.output_toNat, UInt64.toNat_zero] at emptyNat
  rw [remainingOutput_words_safe safe, byteWords_nil state.output emptyNat]
  simp

theorem outputWords_bufferOutputs (state : State) :
    outputWords (bufferOutputs state) = byteWords state.output := by
  by_cases empty : state.output.data.size = 0
  · simp [outputWords, bufferOutputs, empty, byteWords_nil state.output empty]
  · simp [outputWords, bufferOutputs, empty]

theorem consumeStep_written_zero (current : ProcessStep State)
    (zero : current.state.written = 0) :
    (Termination.consumeStep current).state.written = 0 := by
  simp only [Termination.consumeStep]
  split
  · simp only [completeLine]
    split
    · exact zero
    · rfl
  · exact zero

theorem consumeGo_written_zero (fuel : Nat) (current : ProcessStep State)
    (zero : current.state.written = 0) :
    (LeanExe.repeatWhile.go Termination.consumeTest Termination.consumeStep fuel current).state.written = 0 := by
  induction fuel generalizing current with
  | zero => exact zero
  | succ fuel ih =>
      rw [LeanExe.repeatWhile.go]
      split
      · exact ih _ (consumeStep_written_zero current zero)
      · exact zero

theorem consumeInput_written_zero (state : State) (zero : state.written = 0) :
    (consumeInput state).state.written = 0 := by
  exact consumeGo_written_zero _ ⟨true, 0, state⟩ zero

theorem StreamFuture.eof_remaining {state : State} {position : StreamPosition}
    {history expected : List Bytes} (future : StreamFuture state position history expected)
    (eof : state.eof = true) : remainingInput state position = [] := by
  simp [remainingInput, unreadWords, byteWords_nil state.input (future.eof_buffer eof),
    future.eof_input eof]

theorem StreamFuture.eof_room {state : State} {position : StreamPosition}
    {history expected : List Bytes} (future : StreamFuture state position history expected)
    (eof : state.eof = true) (nonempty : state.line.size ≠ 0) :
    StreamModel.Room (bufferModel state history) := by
  apply future.finalRoom _ _ nonempty
  simp only [future.eof_remaining eof, StreamModel.consume_nil]

end Demos.RunningSum
