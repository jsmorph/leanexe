import Demos.RunningSumFp.Program
import LeanExe.Wasi.Process

namespace Demos.RunningSumFp

open LeanExe LeanExe.Wasi

structure State where
  total : Float
  line : Array UInt64
  input : Bytes
  cursor : UInt64
  output : Bytes
  written : UInt64
  eof : Bool

def initial : State := ⟨0, #[], Bytes.empty, 0, Bytes.empty, 0, false⟩

def completeLine (state : State) : ProcessStep State :=
  let parsed := parse state.line
  if !parsed.1 then ⟨false, 28, state⟩
  else
    let total := state.total + parsed.2
    ⟨true, 0, { state with total, line := #[], output := render total, written := 0 }⟩

def consumeInput (state : State) : ProcessStep State :=
  LeanExe.repeatWhile (state.input.size - state.cursor) (ProcessStep.mk true 0 state)
    (fun current => current.running && current.state.output.size == 0 &&
      current.state.cursor < current.state.input.size)
    fun current =>
      let byte := current.state.input.get current.state.cursor
      let next := { current.state with cursor := current.state.cursor + 1 }
      if byte == 10 then completeLine next
      else ⟨true, 0, { next with line := next.line.push byte }⟩

def remainingOutput (state : State) : Bytes :=
  Bytes.build (state.output.size - state.written) fun i => state.output.get (state.written + i)

def afterWrite (state : State) (reply : WriteResult) : ProcessStep State :=
  if reply.errno != 0 then ⟨false, reply.errno, state⟩
  else
    let written := state.written + reply.count
    if written == state.output.size then
      ⟨true, 0, { state with output := Bytes.empty, written := 0 }⟩
    else
      ⟨true, 0, { state with written }⟩

def afterRead (state : State) (reply : ReadResult) : ProcessStep State :=
  if reply.errno != 0 then ⟨false, reply.errno, state⟩
  else
    ⟨true, 0, { state with input := reply.bytes, cursor := 0, eof := reply.bytes.size == 0 }⟩

def writeStep (state : State) : Action (ProcessStep State) := do
  let reply ← writeStdoutSome (remainingOutput state)
  pure (afterWrite state reply)

def readStep (state : State) : Action (ProcessStep State) := do
  let reply ← readSome 4096
  pure (afterRead state reply)

def step (state : State) : Action (ProcessStep State) :=
  if state.written < state.output.size then writeStep state
  else if state.cursor < state.input.size then pure (consumeInput state)
  else if state.eof then
    if state.line.size.toUInt64 == 0 then pure ⟨false, 0, state⟩
    else pure (completeLine state)
  else readStep state

def begin : Action (ProcessStep State) := pure ⟨true, 0, initial⟩

def process : Process State := ⟨initial, step⟩

end Demos.RunningSumFp
