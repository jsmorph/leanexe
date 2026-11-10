import Demos.Rcv.Read

/-!
The word form of the reader's result, which the reader program `readContest` of
`Demos/Rcv/ReadProgram.lean` returns: the contest's words of a well-formed file, and `[0, j, code]`
for a file whose first faulty line is `j` with the role of the code `code`.
-/

namespace Demos.Rcv.Spec

/-- The code of a role in the reader program's result. -/
def Role.code : Role → Nat
  | .format => 0
  | .contest => 1
  | .positions => 2
  | .candidates => 3
  | .candidate => 4
  | .order => 5
  | .ballots => 6
  | .ballot => 7
  | .end => 8

/-- The words of the reader's result on the file `b`. -/
def readResult (b : List UInt8) : List UInt64 :=
  match read b with
  | .ok c => contestWords c
  | .error j r => [0, UInt64.ofNat j, UInt64.ofNat r.code]

end Demos.Rcv.Spec
