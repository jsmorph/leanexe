import Demos.RunningSum.StreamHost
import Demos.RunningSum.StreamBuffer
import Demos.RunningSum.InputBounds

namespace Demos.RunningSum

open LeanExe LeanExe.Wasi

def outputWords (output : List Bytes) : List UInt64 := output.flatMap byteWords

def remainingInput (state : State) (position : StreamPosition) : List UInt64 :=
  unreadWords state ++ position.input

structure StreamFuture (state : State) (position : StreamPosition)
    (history expected : List Bytes) : Prop where
  safe : Termination.Safe state
  normal : state.total.Valid
  eof_buffer : state.eof = true → state.input.data.size = 0
  eof_input : state.eof = true → position.input = []
  output : outputWords history = position.output ++ byteWords (remainingOutput state)
  modelSafe : StreamModel.Safe (bufferModel state history) (remainingInput state position)
  finalRoom : ∀ final, StreamModel.consume (bufferModel state history)
    (remainingInput state position) = .ok final →
      final.pending.size ≠ 0 → StreamModel.Room final
  completion : ∃ processed final,
    StreamModel.consume (bufferModel state history) (remainingInput state position) = .ok processed ∧
      StreamModel.finish processed = .ok final ∧ final.output = expected

theorem streamFuture_initial (position : StreamPosition) (empty : position.output = [])
    (inputs : List (Array UInt64)) (valid : StreamModel.ValidInput position.input inputs)
    (bounds : StreamModel.InputBounds inputs) :
    ∃ expected, StreamFuture initial position [] expected ∧
      List.Forall₂ DecimalOutput (StreamModel.prefixSums 0 inputs) expected := by
  obtain ⟨modelSafe, finalRoom⟩ :=
    StreamModel.validInput_safe_and_finalRoom position.input inputs valid bounds
  obtain ⟨processed, final, consumed, finished, encoded, _⟩ :=
    StreamModel.stream_correct_of_inputBounds position.input inputs valid bounds
  have model : bufferModel initial [] = StreamModel.initial := rfl
  have unread : remainingInput initial position = position.input := rfl
  refine ⟨final.output, ⟨?_, zero_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩, encoded⟩
  · constructor <;> simp [initial, Bytes.size, Bytes.empty]
  · simp [initial]
  · simp [initial]
  · simp [outputWords, remainingOutput, initial, empty, byteWords, Bytes.size, Bytes.build,
      Bytes.empty]
  · simpa only [model, unread] using modelSafe
  · intro result executed _
    apply finalRoom result
    simpa only [model, unread] using executed
  · exact ⟨processed, final, by simpa only [model, unread] using consumed, finished, rfl⟩

end Demos.RunningSum
