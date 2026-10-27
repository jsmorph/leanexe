import Demos.StreamFold.Buffer
import Demos.StreamFold.StreamHost

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

variable {Acc : Type} {kernel : Kernel Acc} (spec : KernelSpec kernel)

def outputWords (output : List Bytes) : List UInt64 := output.flatMap byteWords

def remainingInput (state : BufferState Acc) (position : StreamPosition) : List UInt64 :=
  unreadWords state ++ position.input

structure StreamFuture (state : BufferState Acc) (position : StreamPosition)
    (history expected : List Bytes) (status : UInt64) : Prop where
  safe : Safe state
  normal : spec.Good state.total
  eof_buffer : state.eof = true → state.input.data.size = 0
  eof_input : state.eof = true → position.input = []
  output : outputWords history = position.output ++ byteWords (remainingOutput state)
  modelSafe : Model.Safe spec (bufferModel state history) (remainingInput state position)
  finalRoom : ∀ final, Model.consume kernel (bufferModel state history)
    (remainingInput state position) = .ok final →
      final.pending.size ≠ 0 → spec.Room final.total final.pending
  completion : Model.outcome kernel (bufferModel state history) (remainingInput state position) =
    (expected, status)

/-- The process has written the outputs `expected`, and it has read its whole input when `status`
is 0. -/
structure StreamDone (position : StreamPosition) (expected : List Bytes) (status : UInt64) :
    Prop where
  output : position.output = outputWords expected
  input : status = 0 → position.input = []

theorem streamFuture_initial (seed : Acc) (position : StreamPosition)
    (empty : position.output = []) (good : spec.Good seed)
    (rooms : Model.LineRooms spec seed (Model.lines position.input)) :
    StreamFuture spec (initial seed) position []
      (Model.foldOutcome kernel seed (Model.lines position.input)).1
      (Model.foldOutcome kernel seed (Model.lines position.input)).2 := by
  have model : bufferModel (initial seed) [] = Model.initial seed := rfl
  have unread : remainingInput (initial seed) position = position.input := rfl
  refine ⟨Safe.initial seed, good, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [initial]
  · simp [initial]
  · simp [outputWords, remainingOutput, initial, empty, byteWords, Bytes.size, Bytes.build,
      Bytes.empty]
  · rw [model, unread]
    exact Model.safe_of_rooms spec seed #[] [] position.input rooms
  · intro final executed nonempty
    rw [model, unread] at executed
    exact Model.room_of_rooms spec seed #[] [] position.input rooms executed nonempty
  · rw [model, unread, Model.outcome_initial]

end Demos.StreamFold
