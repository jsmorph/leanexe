import Demos.Rcv.Maine.PrintProgram
import Demos.Rcv.Maine.Program
import Demos.Rcv.ReadProgram

/-!
The export `tabulate` of the Maine module in the verified compiler's dialect: the shared reader
program of `Demos/Rcv/ReadProgram.lean`, the Maine count over words of
`Demos/Rcv/Maine/Program.lean`, and the Maine report's printer of
`Demos/Rcv/Maine/PrintProgram.lean`.  The reader's first word is 0 exactly when the file is
malformed, and then its next two words are the line and the role's code of the error report.  For a
well-formed file the printer takes the mask of the counted candidates, which `countedOf` reads from
the contest's kinds.
-/

namespace Demos.Rcv.Maine.TabulateProgram

open LeanExe Demos.Rcv.ReadProgram

/-- The Maine report of the file `b`: the error report of a malformed file, and the printed count
of a well-formed one. -/
def tabulate (b : Bytes) : Bytes :=
  let ws := readContest b
  if ws[(0 : UInt64).toNat]! == 0 then
    PrintProgram.printError ws[(1 : UInt64).toNat]! ws[(2 : UInt64).toNat]!
  else
    let n := ws[(0 : UInt64).toNat]!
    PrintProgram.printReport b n (Demos.Rcv.Program.countedOf ws n) (Program.count ws)

end Demos.Rcv.Maine.TabulateProgram
