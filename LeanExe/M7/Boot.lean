import LeanExe.M7.Div
import LeanExe.M7.Image

/-!
The image of a program with requests that a Cortex-M7 starts from reset: a vector table, a
self-loop, an initialization, and the generator's program.  Reset reads word 0 of the table into
SP and word 1 into the program counter, with bit 0 of word 1 copied to EPSR.T, which must be set
for Thumb code (DDI 0403E.e sections B1.5.3 and B1.5.5).  Word 1 names the initialization, and
every other entry of the table names the self-loop, with bit 0 set, so that an exception, which
no proved run takes, stops there.  The initialization `init` consists of 32-bit forms that fall
through to `main`, which the generator places after it, so the program's base follows from the
table's length and the initialization's.

`Boot` names the table's address `org`, which is also the address of the image's first byte, the
number of the table's words, the initial SP, and the initialization.  `bootProgram` gives the
instructions from the self-loop on, `bootHalfs` the image's halfwords, the table's words as two
halfwords each, the lower first, and `bootBytes` its bytes, each halfword's low byte first.
`bootFileOk` compares those bytes with the number that `file_nat%` reads from a file.
-/

namespace LeanExe.M7

/-- The layout of an image from reset: the address `org` of the vector table and of the image,
the table's number of words, the initial SP, and the initialization. -/
structure Boot where
  org : UInt32
  entries : Nat
  sp : UInt32
  init : List Instr

/-- The address of the self-loop after the table. -/
def Boot.loop (B : Boot) : UInt32 := after B.org B.entries

/-- The reset entry: the address of the initialization. -/
def Boot.reset (B : Boot) : UInt32 := after B.org (B.entries + 1)

/-- The program's base: the address of `main`, after the initialization. -/
def Boot.base (B : Boot) : UInt32 := after B.org (B.entries + 1 + B.init.length)

/-- The words of the vector table: the initial SP, the reset entry, and the self-loop, each entry
with bit 0 set. -/
def Boot.table (B : Boot) : List UInt32 :=
  B.sp :: (B.reset ||| 1) :: List.replicate (B.entries - 2) (B.loop ||| 1)

/-- The two halfwords of a word, the lower first. -/
def wordHalfs (w : UInt32) : List UInt16 := [w.toUInt16, (w >>> 16).toUInt16]

/-- The instructions of the image from the self-loop on: the self-loop, the initialization, and
the program of step `k` of `m` from the state `s0`, placed at the base, with the stack's limit
`limit`, the device window from `dev`, and the code of `udivmod64`.  The base follows from a table
of at least two words and an initialization of 32-bit forms, which the theorems about the image
require. -/
def bootProgram (B : Boot) (m : Wasm.Module) (k : Nat) (s0 : List UInt64) (limit dev : UInt32) :
    GenM (List Instr) := do
  let prog ← genProgram m k s0 B.base limit dev udivmod64
  return .bTo (-4) :: B.init ++ prog

/-- The halfwords of the image: the table's words and the instructions `is`. -/
def bootHalfs (B : Boot) (is : List Instr) : List UInt16 :=
  B.table.flatMap wordHalfs ++ is.flatMap encode

/-- The bytes of the image. -/
def bootBytes (B : Boot) (is : List Instr) : List UInt8 := (bootHalfs B is).flatMap halfBytes

/-- The generator's result `g` gives an image whose bytes have the number `n` and the length
`len`. -/
def bootFileOk (B : Boot) (g : GenM (List Instr)) (n len : Nat) : Bool :=
  match g with
  | .ok is => LeanExe.FileNat.natOfBytes (bootBytes B is) == n && (bootBytes B is).length == len
  | .error _ => false

end LeanExe.M7
