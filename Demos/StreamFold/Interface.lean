import LeanExe.Dialect.Bytes
import LeanExe.Dialect.RepeatWhile
import LeanExe.Wasi.Process

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

structure LineResult (Acc : Type) where
  valid : Bool
  total : Acc
  output : Bytes

abbrev Kernel (Acc : Type) := Acc → Array UInt64 → LineResult Acc

structure KernelSpec {Acc : Type} (kernel : Kernel Acc) where
  Good : Acc → Prop
  Room : Acc → Array UInt64 → Prop
  lineFits : ∀ {total line}, Room total line → line.size < UInt64.size
  accepted : ∀ {total line}, Good total → Room total line →
    (kernel total line).valid = true →
    Good (kernel total line).total ∧ 0 < (kernel total line).output.data.size
  outputBound : ∀ total line, (kernel total line).valid = true →
    (kernel total line).output.data.size < UInt64.size

structure BufferState (Acc : Type) where
  total : Acc
  line : Array UInt64
  input : Bytes
  cursor : UInt64
  output : Bytes
  written : UInt64
  eof : Bool

variable {Acc : Type}

def initial (seed : Acc) : BufferState Acc :=
  ⟨seed, #[], Bytes.empty, 0, Bytes.empty, 0, false⟩

def completeLine (kernel : Kernel Acc) (state : BufferState Acc) :
    ProcessStep (BufferState Acc) :=
  let result := kernel state.total state.line
  if !result.valid then ⟨false, 28, state⟩
  else ⟨true, 0, { state with total := result.total, line := #[], output := result.output, written := 0 }⟩

def consumeTest (current : ProcessStep (BufferState Acc)) : Bool :=
  current.running && current.state.output.size == 0 &&
    current.state.cursor < current.state.input.size

def consumeStep (kernel : Kernel Acc) (current : ProcessStep (BufferState Acc)) :
    ProcessStep (BufferState Acc) :=
  let byte := current.state.input.get current.state.cursor
  let next := { current.state with cursor := current.state.cursor + 1 }
  if byte == 10 then completeLine kernel next
  else ⟨true, 0, { next with line := next.line.push byte }⟩

def consumeInput (kernel : Kernel Acc) (state : BufferState Acc) : ProcessStep (BufferState Acc) :=
  LeanExe.repeatWhile (state.input.size - state.cursor) ⟨true, 0, state⟩
    consumeTest (consumeStep kernel)

def remainingOutput (state : BufferState Acc) : Bytes :=
  Bytes.build (state.output.size - state.written) fun i => state.output.get (state.written + i)

def afterWrite (state : BufferState Acc) (reply : WriteResult) : ProcessStep (BufferState Acc) :=
  if reply.errno != 0 then ⟨false, reply.errno, state⟩
  else
    let written := state.written + reply.count
    if written == state.output.size then
      ⟨true, 0, { state with output := Bytes.empty, written := 0 }⟩
    else ⟨true, 0, { state with written }⟩

def afterRead (state : BufferState Acc) (reply : ReadResult) : ProcessStep (BufferState Acc) :=
  if reply.errno != 0 then ⟨false, reply.errno, state⟩
  else ⟨true, 0, { state with input := reply.bytes, cursor := 0, eof := reply.bytes.size == 0 }⟩

def writeStep (state : BufferState Acc) : Action (ProcessStep (BufferState Acc)) := do
  let reply ← writeStdoutSome (remainingOutput state)
  pure (afterWrite state reply)

def readStep (state : BufferState Acc) : Action (ProcessStep (BufferState Acc)) := do
  let reply ← readSome 4096
  pure (afterRead state reply)

def step (kernel : Kernel Acc) (state : BufferState Acc) : Action (ProcessStep (BufferState Acc)) :=
  if state.written < state.output.size then writeStep state
  else if state.cursor < state.input.size then pure (consumeInput kernel state)
  else if state.eof then
    if state.line.size.toUInt64 == 0 then pure ⟨false, 0, state⟩
    else pure (completeLine kernel state)
  else readStep state

def process (kernel : Kernel Acc) (seed : Acc) : Process (BufferState Acc) :=
  ⟨initial seed, step kernel⟩

namespace Model

structure State (Acc : Type) where
  total : Acc
  pending : Array UInt64
  output : List Bytes

def emitLine (kernel : Kernel Acc) (state : State Acc) : Except UInt64 (State Acc) :=
  let result := kernel state.total state.pending
  if result.valid then .ok ⟨result.total, #[], state.output ++ [result.output]⟩ else .error 28

def consumeByte (kernel : Kernel Acc) (state : State Acc) (byte : UInt64) :
    Except UInt64 (State Acc) :=
  if byte == 10 then emitLine kernel state
  else .ok { state with pending := state.pending.push byte }

def consume (kernel : Kernel Acc) (state : State Acc) (bytes : List UInt64) :
    Except UInt64 (State Acc) := bytes.foldlM (consumeByte kernel) state

def finish (kernel : Kernel Acc) (state : State Acc) : Except UInt64 (State Acc) :=
  if state.pending.size = 0 then .ok state else emitLine kernel state

def Safe {kernel : Kernel Acc} (spec : KernelSpec kernel) : State Acc → List UInt64 → Prop
  | _, [] => True
  | state, byte :: bytes =>
      (byte = 10 → spec.Room state.total state.pending) ∧
        ∀ next, consumeByte kernel state byte = .ok next → Safe spec next bytes

def initial (seed : Acc) : State Acc := ⟨seed, #[], []⟩

end Model

end Demos.StreamFold
