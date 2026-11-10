import Demos.Rcv.TabulateProgram
import LeanExe.Wasi.Process
import LeanExe.Wasi.ReadAll

/-! The tabulator as a WASI process over stdin and stdout.  `begin` reads the whole standard input
with `readAll limit` into one buffer and replaces it with the report of the input, which
`tabulate` computes.  A read that returns an errno stops the process with that errno, and an input
of more than `limit` bytes stops it with status `tooLong` before `tabulate`.  Each step writes the
rest of the report, continuing after short writes, and the process stops with status 0 when the
report is written.  A write that returns an errno stops the process with that errno. -/

namespace Demos.Rcv.Process

open LeanExe LeanExe.Wasi

/-- The report and the number of its bytes written. -/
structure State where
  output : Bytes
  written : UInt64

def initial : State := ⟨Bytes.empty, 0⟩

/-- The most bytes of input that the process tabulates. -/
def limit : UInt64 := 50000000

/-- The status for an input of more than `limit` bytes: WASI's errno `fbig`, file too large. -/
def tooLong : UInt64 := 22

/-- The bytes of the output that remain to be written. -/
def remainingOutput (s : State) : Bytes :=
  Bytes.build (s.output.size - s.written) fun i => s.output.get (s.written + i)

/-- The step after a write that returned `reply`: an errno stops the process with it, a write that
completes the output clears it, and a shorter write advances `written`. -/
def afterWrite (s : State) (reply : WriteResult) : ProcessStep State :=
  if reply.errno != 0 then ⟨false, reply.errno, s⟩
  else if s.written + reply.count == s.output.size then ⟨true, 0, ⟨Bytes.empty, 0⟩⟩
  else ⟨true, 0, { s with written := s.written + reply.count }⟩

/-- The process after `readAll` returned `input`: an errno or an input of more than `limit` bytes
stops it, and otherwise it holds the report of the input. -/
def started (input : ReadResult) : ProcessStep State :=
  if input.errno != 0 then ⟨false, input.errno, initial⟩
  else if limit < input.bytes.size then ⟨false, tooLong, initial⟩
  else ⟨true, 0, ⟨TabulateProgram.tabulate input.bytes, 0⟩⟩

def writeStep (s : State) : Action (ProcessStep State) := do
  let reply ← writeStdoutSome (remainingOutput s)
  pure (afterWrite s reply)

/-- One step: a write while output remains, and otherwise a stop with status 0. -/
def step (s : State) : Action (ProcessStep State) :=
  if s.written < s.output.size then writeStep s else pure ⟨false, 0, s⟩

def begin : Action (ProcessStep State) := do
  let input ← readAll limit
  pure (started input)

def process : Process State := ⟨initial, step⟩

end Demos.Rcv.Process
