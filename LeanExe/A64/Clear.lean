import LeanExe.A64.Machine

/-!
`clearLoop` stores zero words from the address in X0 up to the address in X1.  Each pass compares
X0 with X1 as unsigned numbers, leaves the loop when X0 is at or above X1, and otherwise stores a
zero word at X0 and adds 8 to X0.  `LeanExe.A64.Proof.Clear` proves its run.
-/

namespace LeanExe.A64

/-- The instructions `CMP X0, X1`, `B.HS` to the word after the loop, `STR XZR, [X0]`,
`ADD X0, X0, #8`, and `B` back to the `CMP`.  The field 4 of `B.HS` reaches four words ahead, and
the field `2 ^ 26 - 4` of `B`, which is -4 as a signed 26-bit number, reaches four words back. -/
def clearLoop : List Instr :=
  [.subsReg 31 0 1, .bcond 2 4, .str 31 0 0, .addImm 0 0 8, .b 67108860]

end LeanExe.A64
