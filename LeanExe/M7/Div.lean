import LeanExe.M7.Encode

/-!
`udivmod64`, the routine that divides a `UInt64` by a nonzero `UInt64` on the Cortex-M7, whose
`UDIV` divides only 32-bit words.  It takes the dividend in r0 and r1 and the divisor in r2 and r3,
each with its low word first, returns the quotient in r0 and r1 and the remainder in r2 and r3,
changes r4 to r7 and the flags, accesses no memory, and returns with `BX LR`.

The routine tests the divisor's low word first.  When it is 0, the quotient is the dividend's high
word divided by the divisor's high word, which `UDIV` gives, and the remainder is the high words'
remainder, which `MLS` gives, as its high word and the dividend's low word as its low word.  When
both high words are 0, `UDIV` and `MLS` give the quotient and the remainder of the low words.
Otherwise `SUBS` and `SBCS` compare the dividend with the divisor, and a dividend below the divisor
is the remainder, with the quotient 0.  Otherwise the routine shifts the divisor left by `s`, the
leading zero count of the divisor less that of the dividend, which `CLZ` gives, and runs `s + 1`
passes of a restoring shift-subtract loop.  Each pass subtracts the shifted divisor from the
remainder with `SUBS` and `SBCS`, shifts the carry, set when the subtraction does not borrow, into
the quotient, adds the divisor back with `ADDS` and `ADC` when the subtraction borrowed, and
halves the shifted divisor.

Every form but `BX LR` takes 4 bytes, and `BX LR` takes 2.  A piece that returns and is followed by
more code ends with a second `BX LR`, which never runs, so that every 32-bit form starts at a
multiple of 4 from the routine's address, as in the code whose cycles were measured on the board.
The pieces lie one after another at these byte offsets from the routine's address: `test` at 0,
`low` at 16, `high` at 32, `compare` at 56, `count` at 68, `shift` at 92, `clear` at 128, `pass` at
136, `done` at 192, and `small` at 212.  Each branch's offset counts from its address plus 4.
-/

namespace LeanExe.M7

namespace Udiv

/-- `CMP r2, #0` and `BEQ high`, then `ORRS r4, r1, r3` and `BNE compare`: the branch to `high`
when the divisor's low word is 0, to `compare` when a high word is not 0, and to `low` otherwise. -/
def test : List Instr :=
  [.cmpImm 2 0, Instr.bcondTo 0 24, .orrReg 1 4 1 3, Instr.bcondTo 1 40]

/-- `UDIV r4, r0, r2`, `MLS r2, r4, r2, r0`, `MOV r0, r4`, and `BX LR`: the quotient and the
remainder of the low words, whose high words r1 and r3 are 0. -/
def low : List Instr := [.udiv 4 0 2, .mls 2 4 2 0, Instr.lslBy 0 4 0, .bxLr, .bxLr]

/-- `UDIV r4, r1, r3`, `MLS r3, r4, r3, r1`, `MOV r2, r0`, `MOV r0, r4`, `MOV r1, #0`, and
`BX LR`: the quotient of the high words, and the remainder of the high words followed by the
dividend's low word. -/
def high : List Instr :=
  [.udiv 4 1 3, .mls 3 4 3 1, Instr.lslBy 2 0 0, Instr.lslBy 0 4 0, .movImm 1 0, .bxLr, .bxLr]

/-- `SUBS r4, r0, r2`, `SBCS r4, r1, r3`, and `BCC small`: the branch to `small` when the dividend
lies below the divisor. -/
def compare : List Instr := [.subReg 1 4 0 2, .sbcReg 1 4 1 3, Instr.bcondTo 3 144]

/-- `CLZ r4, r3`, `CLZ r5, r2`, `LSR r6, r4, #5`, `MLA r4, r5, r6, r4`, `CLZ r5, r1`, and
`SUB r4, r4, r5`: the shift `s` in r4.  The divisor's leading zero count is that of its high word,
or 32 plus that of its low word when the high word is 0, the case in which the high word's count
shifted right by 5 is 1.  The dividend's high word is not 0 here. -/
def count : List Instr :=
  [.clz 4 3, .clz 5 2, Instr.lsrBy 6 4 5, .mla 4 5 6 4, .clz 5 1, .subReg 0 4 4 5]

/-- `LSL r3, r3, r4`, `MOV r5, #32`, `SUB r5, r5, r4`, `LSR r5, r2, r5`, `ORR r3, r3, r5`,
`SUB r5, r4, #32`, `LSL r5, r2, r5`, `ORR r3, r3, r5`, and `LSL r2, r2, r4`: the divisor shifted
left by `s`, as CompCert's `LSHL` computes it. -/
def shift : List Instr :=
  [.lslReg 3 3 4, .movImm 5 32, .subReg 0 5 5 4, .lsrReg 5 2 5, .orrReg 0 3 3 5, .subImm 5 4 32,
    .lslReg 5 2 5, .orrReg 0 3 3 5, .lslReg 2 2 4]

/-- `MOV r5, #0` and `MOV r6, #0`: the quotient 0. -/
def clear : List Instr := [.movImm 5 0, .movImm 6 0]

/-- A pass of the loop, with the remainder in r0 and r1, the shifted divisor in r2 and r3, the
passes left less 1 in r4, and the quotient in r5 and r6: `SUBS r0, r0, r2`, `SBCS r1, r1, r3`,
`LSR r7, r5, #31`, `ADD r6, r7, r6, LSL #1`, `ADC r5, r5, r5`, `BCS keep`, `ADDS r0, r0, r2`,
`ADC r1, r1, r3`, and at `keep`, `LSR r2, r2, #1`, `ADD r2, r2, r3, LSL #31`, `LSR r3, r3, #1`,
`CMP r4, #0`, `SUB r4, r4, #1`, and `BNE pass`. -/
def pass : List Instr :=
  [.subReg 1 0 0 2, .sbcReg 1 1 1 3, Instr.lsrBy 7 5 31, Instr.addLsl 0 6 7 6 1, .adcReg 5 5 5,
    Instr.bcondTo 2 8, Instr.addLsl 1 0 0 2 0, .adcReg 1 1 3, Instr.lsrBy 2 2 1,
    Instr.addLsl 0 2 2 3 31, Instr.lsrBy 3 3 1, .cmpImm 4 0, .subImm 4 4 1, Instr.bcondTo 1 (-56)]

/-- `MOV r2, r0`, `MOV r3, r1`, `MOV r0, r5`, `MOV r1, r6`, and `BX LR`: the loop's results. -/
def done : List Instr :=
  [Instr.lslBy 2 0 0, Instr.lslBy 3 1 0, Instr.lslBy 0 5 0, Instr.lslBy 1 6 0, .bxLr, .bxLr]

/-- `MOV r2, r0`, `MOV r3, r1`, `MOV r0, #0`, `MOV r1, #0`, and `BX LR`: the remainder of a
dividend below the divisor. -/
def small : List Instr := [Instr.lslBy 2 0 0, Instr.lslBy 3 1 0, .movImm 0 0, .movImm 1 0, .bxLr]

end Udiv

/-- The routine that divides the `UInt64` in r0 and r1 by the nonzero `UInt64` in r2 and r3. -/
def udivmod64 : List Instr :=
  Udiv.test ++ Udiv.low ++ Udiv.high ++ Udiv.compare ++ Udiv.count ++ Udiv.shift ++ Udiv.clear ++
    Udiv.pass ++ Udiv.done ++ Udiv.small

end LeanExe.M7
