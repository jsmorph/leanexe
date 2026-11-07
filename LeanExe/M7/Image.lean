import LeanExe.A64.File
import LeanExe.M7.Gen

/-!
The bytes of generated Thumb-2 code.  `imageBytes` lays out each instruction's halfwords, the first
at the lower address, each with its low byte first, the order in which the processor fetches them
(DDI 0403E.e section A3.3.1).  `fileOk` compares those bytes with the number that `file_nat%` of
`LeanExe/A64/File.lean` reads from a file, so that the kernel's evaluation of the generator checks
the file that the board's flash receives.
-/

namespace LeanExe.M7

/-- The two bytes of a halfword, the low byte first. -/
def halfBytes (h : UInt16) : List UInt8 := [h.toUInt8, (h >>> 8).toUInt8]

/-- The bytes of the instructions `is`. -/
def imageBytes (is : List Instr) : List UInt8 :=
  is.flatMap fun i => (encode i).flatMap halfBytes

/-- The generator's result `g` is code whose bytes have the number `n` and the length `len`. -/
def fileOk (g : Except String (List Instr)) (n len : Nat) : Bool :=
  match g with
  | .ok is => LeanExe.A64.natOfBytes (imageBytes is) == n && (imageBytes is).length == len
  | .error _ => false

end LeanExe.M7
