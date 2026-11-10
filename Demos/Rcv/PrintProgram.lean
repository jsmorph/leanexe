import Demos.Rcv.ReadProgram
import Library.Numerics.Decimal.Int64Text.Program

/-!
The report's printer in the verified compiler's dialect.  `printReport b n res` prints the report of
the well-formed file `b` of `n` candidates from the count's result words `res` of the requirements'
section "Word forms of the count", and `printError j code` prints the error report of line `j` with
the role of the code `code` that `readContest` returns.

The printer collects the report's bytes in an array of words, one byte to a word, and copies them
into a buffer at the end.  The texts of the report are words of eight bytes, least significant
first, that `pushWord` appends, and `pushNumber` appends the decimal digits of a word with the
library's `digitCount` and `digitByte` of `Library.Numerics.Decimal.Int64Text`.  The report repeats
lines 2 to `6 + n` of the file byte for byte, and `printReport` copies them from `b`: they run from
byte 14, after `rcv-ballots 1` and its LF, to the position after the LF of line `6 + n`.  Round `r`,
counted from 0, starts at word `2 + r (n + 9)` of the result, whose words give the mask of the
continuing set, `T`, the votes of candidates 1 to `n`, the inactive counts, the elimination's code,
the mask of the eliminated candidates, and the mask of the tied set.  A mask's members print in
increasing index, each after a space.
-/

namespace Demos.Rcv.PrintProgram

open LeanExe
open Demos.Rcv.ReadProgram (findByte)
open Library.Numerics.Decimal.Int64Text (digitCount digitByte)

/-- `out` followed by bytes 0 to `len - 1` of `w`, least significant first. -/
def pushWord (out : Array UInt64) (w len : UInt64) : Array UInt64 :=
  LeanExe.loop len out fun i o => o.push ((w >>> (8 * i)) &&& 255)

/-- `out` followed by the decimal digits of `v`, most significant first. -/
def pushNumber (out : Array UInt64) (v : UInt64) : Array UInt64 :=
  let len := digitCount v
  LeanExe.loop len out fun i o => o.push (digitByte v (len - 1 - i))

/-- `out` followed by the bytes of `b` from `s` to `e`. -/
def pushRange (out : Array UInt64) (b : Bytes) (s e : UInt64) : Array UInt64 :=
  LeanExe.loop (e - s) out fun i o => o.push (b.get (s + i))

/-- `out` followed by the report's first two lines, `rcv-report 1` and `rule ` with the rule
identifier, each with its LF. -/
def pushHead (out : Array UInt64) : Array UInt64 :=
  let o := pushWord out 0x6f7065722d766372 8
  let o := pushWord o 0x6c75720a31207472 8
  let o := pushWord o 0x6e616c6b616f2065 8
  let o := pushWord o 0x7220353031312d64 8
  let o := pushWord o 0x206e6f6973697665 8
  let o := pushWord o 0x616c6b614f202c31 8
  let o := pushWord o 0x207974694320646e 8
  let o := pushWord o 0x2072657472616843 8
  let o := pushWord o 0x736e6f6974636573 8
  let o := pushWord o 0x6e61203330313120 8
  let o := pushWord o 0x2820353031312064 8
  let o := pushWord o 0x7972617572626546 8
  let o := pushWord o 0x202c293730303220 8
  let o := pushWord o 0x656c45202e6c6143 8
  let o := pushWord o 0x2065646f43202e63 8
  let o := pushWord o 0x736e6f6974636573 8
  let o := pushWord o 0x2820313433353120 8
  let o := pushWord o 0x2064657461647075 8
  let o := pushWord o 0x2d31302d39393931 8
  let o := pushWord o 0x20646e6120293130 8
  let o := pushWord o 0x2964283234333531 8
  let o := pushWord o 0x6574616470752820 8
  let o := pushWord o 0x302d323130322064 8
  let o := pushWord o 0x74202c2931302d31 8
  let o := pushWord o 0x6165722073747865 8
  let o := pushWord o 0x312d363230322064 8
  pushWord o 0xa39302d31 5

/-- `out` followed by a line of a text, bytes 0 to `l1 - 1` of `w1` and 0 to `l2 - 1` of `w2`,
then the number `v` and LF. -/
def pushLine (out : Array UInt64) (w1 l1 w2 l2 v : UInt64) : Array UInt64 :=
  (pushNumber (pushWord (pushWord out w1 l1) w2 l2) v).push 10

/-- `out` followed by a space and the index `i + 1` for each bit `i` of `mask` below `n`, in
increasing order. -/
def pushMembers (out : Array UInt64) (mask n : UInt64) : Array UInt64 :=
  LeanExe.loop n out fun i o =>
    if (mask >>> i) &&& 1 == 1 then pushNumber (o.push 32) (i + 1) else o

/-- `out` followed by the line `votes i v` of each candidate `i` of the mask at word `base` of
`res`, with its votes at word `base + 1 + i`. -/
def pushVotes (out : Array UInt64) (res : Array UInt64) (n base : UInt64) : Array UInt64 :=
  let mask := res[base.toNat]!
  LeanExe.loop n out fun i o =>
    if (mask >>> i) &&& 1 == 1 then
      (pushNumber ((pushNumber (pushWord o 0x207365746f76 6) (i + 1)).push 32)
        res[(base + 2 + i).toNat]!).push 10
    else o

/-- `out` followed by the lines of the elimination of the code `code`, with the masks `elim` of the
eliminated candidates and `tied` of the tied set: none for 0, `eliminate lowest` for 1, `tie` and
`eliminate order` for 2, and `eliminate batch` for 3. -/
def pushElimination (out : Array UInt64) (code elim tied n : UInt64) : Array UInt64 :=
  if code == 1 then
    (pushMembers (pushWord (pushWord out 0x74616e696d696c65 8) 0x747365776f6c2065 8) elim n).push 10
  else if code == 2 then
    let o := (pushMembers (pushWord out 0x656974 3) tied n).push 10
    (pushMembers (pushWord (pushWord o 0x74616e696d696c65 8) 0x726564726f2065 7) elim n).push 10
  else if code == 3 then
    (pushMembers (pushWord (pushWord out 0x74616e696d696c65 8) 0x68637461622065 7) elim n).push 10
  else out

/-- `out` followed by the lines of round `r`, whose words start at word `base` of `res`. -/
def pushRoundLines (out : Array UInt64) (res : Array UInt64) (n base r : UInt64) : Array UInt64 :=
  let o := pushLine out 0x20646e756f72 6 0 0 r
  let o := pushLine o 0x69756e69746e6f63 8 0x20676e 3 res[(base + 1).toNat]!
  let o := pushVotes o res n base
  let o := pushLine o 0x6576697463616e69 8 0x206b6e616c6220 7 res[(base + 2 + n).toNat]!
  let o := pushWord o 0x6576697463616e69 8
  let o := pushLine o 0x746e756f636e7520 8 0x206465 3 res[(base + 3 + n).toNat]!
  let o := pushWord o 0x6576697463616e69 8
  let o := pushLine o 0x746f767265766f20 8 0x2065 2 res[(base + 4 + n).toNat]!
  let o := pushWord o 0x6576697463616e69 8
  let o := pushLine o 0x7473756168786520 8 0x206465 3 res[(base + 5 + n).toNat]!
  pushElimination o res[(base + 6 + n).toNat]! res[(base + 7 + n).toNat]!
    res[(base + 8 + n).toNat]! n

/-- The bytes of the words `o`, one byte to a word. -/
def toBytes (o : Array UInt64) : Bytes :=
  Bytes.build o.size.toUInt64 fun i => o[i.toNat]!

/-- The report of the well-formed file `b` of `n` candidates from the count's result words `res`:
the first two lines, lines 2 to `6 + n` of the file, the lines of each round, and the winner. -/
def printReport (b : Bytes) (n : UInt64) (res : Array UInt64) : Bytes :=
  let h := LeanExe.loop (6 + n) 0 fun _ p => findByte b 10 p b.size + 1
  let o := pushRange (pushHead #[]) b 14 h
  let rounds := res[(1 : UInt64).toNat]!
  let o := LeanExe.loop rounds o fun r o => pushRoundLines o res n (2 + r * (n + 9)) (r + 1)
  let w := res[(2 + rounds * (n + 9)).toNat]!
  let o :=
    if w == 0 then pushWord (pushWord o 0x6e2072656e6e6977 8) 0xa656e6f 4
    else (pushNumber (pushWord o 0x2072656e6e6977 7) w).push 10
  toBytes o

/-- `out` followed by the word of the role of the code `code`. -/
def pushRole (out : Array UInt64) (code : UInt64) : Array UInt64 :=
  if code == 0 then pushWord out 0x74616d726f66 6
  else if code == 1 then pushWord out 0x747365746e6f63 7
  else if code == 2 then pushWord (pushWord out 0x6e6f697469736f70 8) 0x73 1
  else if code == 3 then pushWord (pushWord out 0x74616469646e6163 8) 0x7365 2
  else if code == 4 then pushWord (pushWord out 0x74616469646e6163 8) 0x65 1
  else if code == 5 then pushWord out 0x726564726f 5
  else if code == 6 then pushWord out 0x73746f6c6c6162 7
  else if code == 7 then pushWord out 0x746f6c6c6162 6
  else pushWord out 0x646e65 3

/-- The error report of line `j` with the role of the code `code`. -/
def printError (j code : UInt64) : Bytes :=
  let o := pushNumber (pushWord (pushHead #[]) 0x20726f727265 6) j
  toBytes ((pushRole (o.push 32) code).push 10)

end Demos.Rcv.PrintProgram
