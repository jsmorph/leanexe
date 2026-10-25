import Demos.StreamFold.Buffer
import Demos.RunningSum.StreamHost

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

abbrev StreamPosition := Demos.RunningSum.StreamPosition
abbrev StreamHost {World : Type} (host : Host World) (rep : StreamPosition → World → Prop) :=
  Demos.RunningSum.StreamHost host rep

variable {Acc : Type} {kernel : Kernel Acc} (spec : KernelSpec kernel)

def outputWords (output : List Bytes) : List UInt64 := output.flatMap byteWords

def remainingInput (state : BufferState Acc) (position : StreamPosition) : List UInt64 :=
  unreadWords state ++ position.input

structure StreamFuture (state : BufferState Acc) (position : StreamPosition)
    (history expected : List Bytes) : Prop where
  safe : Safe state
  normal : spec.Good state.total
  eof_buffer : state.eof = true → state.input.data.size = 0
  eof_input : state.eof = true → position.input = []
  output : outputWords history = position.output ++ byteWords (remainingOutput state)
  modelSafe : Model.Safe spec (bufferModel state history) (remainingInput state position)
  finalRoom : ∀ final, Model.consume kernel (bufferModel state history)
    (remainingInput state position) = .ok final →
      final.pending.size ≠ 0 → spec.Room final.total final.pending
  completion : ∃ processed final,
    Model.consume kernel (bufferModel state history) (remainingInput state position) = .ok processed ∧
      Model.finish kernel processed = .ok final ∧ final.output = expected

theorem streamFuture_initial (seed : Acc) (position : StreamPosition)
    (empty : position.output = []) (good : spec.Good seed) (expected : List Bytes)
    (modelSafe : Model.Safe spec (Model.initial seed) position.input)
    (finalRoom : ∀ final, Model.consume kernel (Model.initial seed) position.input = .ok final →
      final.pending.size ≠ 0 → spec.Room final.total final.pending)
    (completion : ∃ processed final,
      Model.consume kernel (Model.initial seed) position.input = .ok processed ∧
      Model.finish kernel processed = .ok final ∧ final.output = expected) :
    StreamFuture spec (initial seed) position [] expected := by
  have model : bufferModel (initial seed) [] = Model.initial seed := rfl
  have unread : remainingInput (initial seed) position = position.input := rfl
  refine ⟨Safe.initial seed, good, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [initial]
  · simp [initial]
  · simp [outputWords, remainingOutput, initial, empty, byteWords, Bytes.size, Bytes.build,
      Bytes.empty]
  · simpa only [model, unread] using modelSafe
  · intro final executed nonempty
    exact finalRoom final (by simpa only [model, unread] using executed) nonempty
  · simpa only [model, unread] using completion

end Demos.StreamFold
