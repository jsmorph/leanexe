import Demos.Rcv.Maine.TabulateProgram
import Demos.Rcv.Process

/-! The Maine module as a WASI process over stdin and stdout.  The process is the Oakland
tabulator's process of `Demos/Rcv/Process.lean` with the Maine report in place of Oakland's: the
state, the limit, the status `tooLong`, and the steps, which write the rest of the report, are the
Oakland process's, and `begin` reads the whole standard input with `readAll limit` into one buffer
and replaces it with the Maine report of the input, which
`Demos.Rcv.Maine.TabulateProgram.tabulate` computes.  A read that returns an errno stops the
process with that errno, and an input of more than `limit` bytes stops it with status `tooLong`
before `tabulate`. -/

namespace Demos.Rcv.Maine.Process

open LeanExe LeanExe.Wasi
open Demos.Rcv.Process (State initial limit tooLong)

/-- The process after `readAll` returned `input`: an errno or an input of more than `limit` bytes
stops it, and otherwise it holds the Maine report of the input. -/
def started (input : ReadResult) : ProcessStep State :=
  if input.errno != 0 then ⟨false, input.errno, initial⟩
  else if limit < input.bytes.size then ⟨false, tooLong, initial⟩
  else ⟨true, 0, ⟨TabulateProgram.tabulate input.bytes, 0⟩⟩

def begin : Action (ProcessStep State) := do
  let input ← readAll limit
  pure (started input)

end Demos.Rcv.Maine.Process
