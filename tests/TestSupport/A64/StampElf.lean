import TestSupport.A64.Flip
import LeanExe.A64.Stamp

/-!
`flipBit5` of `TestSupport.A64.Flip` as the stamp program: `stampElf` is the file that
`genStampElf` writes for the function, with the limit `stampInMax` of 8,799,968 bytes of the input
file, so that the function's input of the clock's 16 bytes, 16 random bytes, and the file's bytes
holds at most 8,800,000 bytes, the stack's room of `TestSupport.A64.Programs`, the cap `flipCap`,
and the paths `stamp.in` and `stamp.out`.
-/

namespace TestSupport.A64.StampElf

open LeanExe LeanExe.A64 TestSupport.A64.Flip

/-- The most bytes of the input file. -/
def stampInMax : UInt64 := 8799968

/-- The input path, `stamp.in`. -/
def inPath : List UInt8 := "stamp.in".toUTF8.toList

/-- The output path, `stamp.out`. -/
def outPath : List UInt8 := "stamp.out".toUTF8.toList

/-- The stamp executable of `flipBit5`. -/
def stampElf : Except String (List UInt8 × ElfLayout) :=
  genStampElf compiled.module entry stampInMax room flipCap inPath outPath

end TestSupport.A64.StampElf
