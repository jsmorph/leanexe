import Demos.Rcv.PrintProgram

/-!
The Maine report's printer in the verified compiler's dialect.  `printReport b n counted res`
prints the report of the well-formed file `b` of `n` candidates, whose counted set has the mask
`counted`, from the Maine count's result words `res` of [the requirements](requirements.md),
section "Word forms of the count", and `printError j code` prints the error report of line `j` with
the role of the code `code` that `readContest` returns.

The printer is the Oakland printer of `Demos/Rcv/PrintProgram.lean` with this module's rule line
and the `first` lines.  `pushHead` appends the first two lines with the Maine rule identifier, and
`pushFirst` appends the line `first i f(i)` of each counted candidate `i` in increasing index, with
`f(i)` at word `1 + i` of the result.  The result words of the rounds start after the `n` first
counts, so round `r`, counted from 0, starts at word `2 + n + r (n + 9)`, and the Oakland
`pushRoundLines` prints it.
-/

namespace Demos.Rcv.Maine.PrintProgram

open LeanExe
open Demos.Rcv.ReadProgram (findByte)
open Demos.Rcv.PrintProgram (pushWord pushNumber pushRange pushRoundLines toBytes pushRole)

/-- `out` followed by the report's first two lines, `rcv-report 1` and `rule ` with this module's
rule identifier, each with its LF. -/
def pushHead (out : Array UInt64) : Array UInt64 :=
  let o := pushWord out 0x6f7065722d766372 8
  let o := pushWord o 0x6c75720a31207472 8
  let o := pushWord o 0x2d656e69616d2065 8
  let o := pushWord o 0x7665722061333237 8
  let o := pushWord o 0x2c31206e6f697369 8
  let o := pushWord o 0x2e4d20412d313220 8
  let o := pushWord o 0x636573202e532e52 8
  let o := pushWord o 0x2c3120736e6f6974 8
  let o := pushWord o 0x3733202c31373320 8
  let o := pushWord o 0x363936202c412d34 8
  let o := pushWord o 0x2c412d323237202c 8
  let o := pushWord o 0x202c412d33323720 8
  let o := pushWord o 0x2032333720646e61 8
  let o := pushWord o 0x6572727563207361 8
  let o := pushWord o 0x756f72687420746e 8
  let o := pushWord o 0x2d36323032206867 8
  let o := pushWord o 0x73282031302d3031 8
  let o := pushWord o 0x37206e6f69746365 8
  let o := pushWord o 0x20736120412d3332 8
  let o := pushWord o 0x206465646e656d61 8
  let o := pushWord o 0x3032204c50207962 8
  let o := pushWord o 0x3633202e63203532 8
  let o := pushWord o 0x6365666665202c33 8
  let o := pushWord o 0x3230322065766974 8
  let o := pushWord o 0x2934322d39302d35 8
  let o := pushWord o 0x3035322d3932202c 8
  let o := pushWord o 0x202e522e4d2e4320 8
  let o := pushWord o 0x20353335202e6863 8
  let o := pushWord o 0x6974636566666528 8
  let o := pushWord o 0x2d38313032206576 8
  let o := pushWord o 0x202c2937302d3131 8
  let o := pushWord o 0x6572207374786574 8
  let o := pushWord o 0x2d36323032206461 8
  pushWord o 0xa30312d3131 6

/-- `out` followed by the line `first i f(i)` of each candidate `i` whose bit `i - 1` the mask
`counted` holds, among the first `n`, in increasing index, with `f(i)` at word `1 + i` of `res`. -/
def pushFirst (out res : Array UInt64) (n counted : UInt64) : Array UInt64 :=
  LeanExe.loop n out fun i o =>
    if (counted >>> i) &&& 1 == 1 then
      (pushNumber ((pushNumber (pushWord o 0x207473726966 6) (i + 1)).push 32)
        res[(2 + i).toNat]!).push 10
    else o

/-- The report of the well-formed file `b` of `n` candidates with the counted mask `counted` from
the count's result words `res`: the first two lines, lines 2 to `6 + n` of the file, the `first`
lines, the lines of each round, and the winner. -/
def printReport (b : Bytes) (n counted : UInt64) (res : Array UInt64) : Bytes :=
  let h := LeanExe.loop (6 + n) 0 fun _ p => findByte b 10 p b.size + 1
  let o := pushRange (pushHead #[]) b 14 h
  let o := pushFirst o res n counted
  let rounds := res[(1 : UInt64).toNat]!
  let o := LeanExe.loop rounds o fun r o =>
    pushRoundLines o res n (2 + n + r * (n + 9)) (r + 1)
  let w := res[(2 + n + rounds * (n + 9)).toNat]!
  let o :=
    if w == 0 then pushWord (pushWord o 0x6e2072656e6e6977 8) 0xa656e6f 4
    else (pushNumber (pushWord o 0x2072656e6e6977 7) w).push 10
  toBytes o

/-- The error report of line `j` with the role of the code `code`. -/
def printError (j code : UInt64) : Bytes :=
  let o := pushNumber (pushWord (pushHead #[]) 0x20726f727265 6) j
  toBytes ((pushRole (o.push 32) code).push 10)

end Demos.Rcv.Maine.PrintProgram
