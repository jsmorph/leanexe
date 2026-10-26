import Demos.RunningSum.Stream
import Demos.StreamFold.Map
import LeanExe.Wasi.ProcessRelated

namespace Demos.RunningSum

open LeanExe LeanExe.Wasi

def lineKernel (total : Decimal) (line : Array UInt64) : StreamFold.LineResult Decimal :=
  let parsed := parse line
  let next := add total parsed.value
  ⟨parsed.valid, next, render next⟩

def bufferState (state : State) : StreamFold.BufferState Decimal :=
  ⟨state.total, state.line, state.input, state.cursor, state.output, state.written, state.eof⟩

def bufferResult (result : ProcessStep State) : ProcessStep (StreamFold.BufferState Decimal) :=
  ⟨result.running, result.status, bufferState result.state⟩

theorem buffer_initial : bufferState initial = StreamFold.initial zero := rfl

theorem buffer_completeLine (state : State) :
    bufferResult (completeLine state) = StreamFold.completeLine lineKernel (bufferState state) := by
  dsimp only [completeLine, StreamFold.completeLine, lineKernel, bufferState, bufferResult]
  split <;> simp_all

private def inputTest (current : ProcessStep State) : Bool :=
  current.running && current.state.output.size == 0 &&
    current.state.cursor < current.state.input.size

private def inputStep (current : ProcessStep State) : ProcessStep State :=
  let byte := current.state.input.get current.state.cursor
  let next := { current.state with cursor := current.state.cursor + 1 }
  if byte == 10 then completeLine next
  else ⟨true, 0, { next with line := next.line.push byte }⟩

private theorem buffer_inputStep (current : ProcessStep State) :
    bufferResult (inputStep current) = StreamFold.consumeStep lineKernel (bufferResult current) := by
  dsimp only [inputStep, StreamFold.consumeStep, bufferResult, bufferState]
  split
  · exact buffer_completeLine _
  · rfl

theorem buffer_consumeInput (state : State) :
    bufferResult (consumeInput state) = StreamFold.consumeInput lineKernel (bufferState state) :=
  StreamFold.repeatWhile_map bufferResult inputTest StreamFold.consumeTest inputStep
    (StreamFold.consumeStep lineKernel) (fun _ => rfl) buffer_inputStep _ _

theorem buffer_afterWrite (state : State) (reply : WriteResult) :
    bufferResult (afterWrite state reply) = StreamFold.afterWrite (bufferState state) reply := by
  dsimp only [afterWrite, StreamFold.afterWrite, bufferResult, bufferState]
  split
  · rfl
  · split <;> rfl

theorem buffer_afterRead (state : State) (reply : ReadResult) :
    bufferResult (afterRead state reply) = StreamFold.afterRead (bufferState state) reply := by
  dsimp only [afterRead, StreamFold.afterRead, bufferResult, bufferState]
  split <;> rfl

private theorem result_related {native : ProcessStep State}
    {flat : ProcessStep (StreamFold.BufferState Decimal)} (same : flat = bufferResult native) :
    ProcessStep.Rel (fun native flat => flat = bufferState native) native flat := by
  subst flat
  exact ⟨rfl, rfl, rfl⟩

theorem buffer_step_related (state : State) :
    Action.Rel (ProcessStep.Rel (fun native flat => flat = bufferState native))
      (step state) (StreamFold.step lineKernel (bufferState state)) := by
  dsimp only [step, StreamFold.step, bufferState]
  split
  · change Action.Rel _
      (.write .stdout (remainingOutput state) fun reply => .pure (afterWrite state reply))
      (.write .stdout (remainingOutput state) fun reply =>
        .pure (StreamFold.afterWrite (bufferState state) reply))
    exact .write .stdout _ fun reply => .pure (result_related (buffer_afterWrite state reply).symm)
  · split
    · exact .pure (result_related (buffer_consumeInput state).symm)
    · split
      · split
        · exact .pure ⟨rfl, rfl, rfl⟩
        · exact .pure (result_related (buffer_completeLine state).symm)
      · change Action.Rel _
          (.read 4096 fun reply => .pure (afterRead state reply))
          (.read 4096 fun reply => .pure (StreamFold.afterRead (bufferState state) reply))
        exact .read 4096 fun reply => .pure (result_related (buffer_afterRead state reply).symm)

theorem buffer_related : Process.Rel (fun native flat => flat = bufferState native)
    process (StreamFold.process lineKernel zero) := by
  intro native flat same
  subst flat
  exact buffer_step_related native

end Demos.RunningSum
