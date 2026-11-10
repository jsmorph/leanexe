import Demos.Rcv.TabulateProgram
import LeanExe.Wasi.Process

/-! The tabulator as a WASI process over stdin and stdout.  The process reads its standard input
in reads of at most 4,096 bytes and appends each read's bytes to the input it holds.  At EOF it
replaces the input with the report of the whole input, which `tabulate` computes, and writes the
report to its standard output, continuing after short writes, and then stops with status 0.  A
read or a write that returns an errno stops the process with that errno. -/

namespace Demos.Rcv.Process

open LeanExe LeanExe.Wasi

/-- The input read so far, the report once the input has ended, the number of the report's bytes
written, and whether a read has reported EOF. -/
structure State where
  input : Bytes
  output : Bytes
  written : UInt64
  eof : Bool

def initial : State := ⟨Bytes.empty, Bytes.empty, 0, false⟩

/-- The bytes of `a` followed by those of `b`. -/
def append (a b : Bytes) : Bytes :=
  Bytes.build (a.size + b.size) fun i => if i < a.size then a.get i else b.get (i - a.size)

/-- The bytes of the output that remain to be written. -/
def remainingOutput (s : State) : Bytes :=
  Bytes.build (s.output.size - s.written) fun i => s.output.get (s.written + i)

/-- The step after a write that returned `reply`: an errno stops the process with it, a write that
completes the output clears it, and a shorter write advances `written`. -/
def afterWrite (s : State) (reply : WriteResult) : ProcessStep State :=
  if reply.errno != 0 then ⟨false, reply.errno, s⟩
  else if s.written + reply.count == s.output.size then
    ⟨true, 0, { s with output := Bytes.empty, written := 0 }⟩
  else ⟨true, 0, { s with written := s.written + reply.count }⟩

/-- The step after a read that returned `reply`: an errno stops the process with it, an empty read
replaces the input with its report, and other bytes extend the input. -/
def afterRead (s : State) (reply : ReadResult) : ProcessStep State :=
  if reply.errno != 0 then ⟨false, reply.errno, s⟩
  else if reply.bytes.size == 0 then
    ⟨true, 0, ⟨Bytes.empty, TabulateProgram.tabulate s.input, 0, true⟩⟩
  else ⟨true, 0, { s with input := append s.input reply.bytes }⟩

def writeStep (s : State) : Action (ProcessStep State) := do
  let reply ← writeStdoutSome (remainingOutput s)
  pure (afterWrite s reply)

def readStep (s : State) : Action (ProcessStep State) := do
  let reply ← readSome 4096
  pure (afterRead s reply)

/-- One step: a write while output remains, otherwise a stop with status 0 after EOF, and
otherwise a read. -/
def step (s : State) : Action (ProcessStep State) :=
  if s.written < s.output.size then writeStep s
  else if s.eof then pure ⟨false, 0, s⟩
  else readStep s

def begin : Action (ProcessStep State) := pure ⟨true, 0, initial⟩

def process : Process State := ⟨initial, step⟩

end Demos.Rcv.Process
