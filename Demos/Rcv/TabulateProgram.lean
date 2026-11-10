import Demos.Rcv.PrintProgram
import Demos.Rcv.Program

/-!
The export `tabulate` of the Oakland tabulator in the verified compiler's dialect: the reader
program of `Demos/Rcv/ReadProgram.lean`, the count over words of `Demos/Rcv/Program.lean`, and the
report's printer of `Demos/Rcv/PrintProgram.lean`.  The reader's first word is 0 exactly when the
file is malformed, and then its next two words are the line and the role's code of the error
report.
-/

namespace Demos.Rcv.TabulateProgram

open LeanExe Demos.Rcv.ReadProgram Demos.Rcv.PrintProgram

/-- The report of the file `b`: the error report of a malformed file, and the printed count of a
well-formed one. -/
def tabulate (b : Bytes) : Bytes :=
  let ws := readContest b
  if ws[(0 : UInt64).toNat]! == 0 then printError ws[(1 : UInt64).toNat]! ws[(2 : UInt64).toNat]!
  else printReport b ws[(0 : UInt64).toNat]! (Demos.Rcv.Program.count ws)

end Demos.Rcv.TabulateProgram
