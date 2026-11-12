import TestSupport.A64.Flip
import LeanExe.A64.Elf

/-!
`flipBit5` of `TestSupport.A64.Flip` as a Linux executable: `elf` is the file that `genSysElf`
writes for the function, with the limit `inMax` of 8,800,000 bytes, the stack's room of
`TestSupport.A64.Programs`, and the cap `flipCap`.  The executable reads standard input to its end
and writes the input with bit 5 of each byte flipped to standard output.  `cases` lists the lengths
of the messages of the runs of `tests/linux/a64-elf.sh`, and `overLengths` the lengths above
`inMax`, on which the run must end with status 64 and no output.
-/

namespace TestSupport.A64.FlipElf

open LeanExe LeanExe.A64 TestSupport.A64.Flip

/-- The executable of `flipBit5`. -/
def elf : Except String (List UInt8 × ElfLayout) :=
  genSysElf compiled.module entry inMax room flipCap

/-- The lengths of the messages of the runs. -/
def cases : List Nat := [0, 1, 4095, 4096, 65536, 1000000, 8800000]

/-- The lengths above `inMax` of the runs. -/
def overLengths : List Nat := [8800001]

/-- The message of `n` bytes of a run, `TestSupport.A64.Flip.message n`, as a byte array. -/
def messageArray (n : Nat) : ByteArray := Id.run do
  let mut a := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    a := a.push (UInt8.ofNat (i * 131 + i / 251))
  return a

/-- The message `b` with bit 5 of each byte flipped. -/
def flipArray (b : ByteArray) : ByteArray := Id.run do
  let mut a := ByteArray.emptyWithCapacity b.size
  for i in [0:b.size] do
    a := a.push (b.get! i ^^^ 32)
  return a

end TestSupport.A64.FlipElf
