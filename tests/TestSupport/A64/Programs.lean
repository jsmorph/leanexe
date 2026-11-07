import TestSupport.Native.Gcd
import TestSupport.Bare.Programs
import TestSupport.A64.CicTable
import Verified.Examples.Fold
import Demos.Euler.Verified
import LeanExe.Native.Bare
import LeanExe.A64.BootImage

/-!
The bare-metal programs of the AArch64 back end, the counterparts of the programs of
`tests/baremetal/programs.sh` that it covers so far: GCD's loop and GCD's recursion on 1071 and 462,
CRC-32 of the 9 bytes of `123456789`, SHA-256 of the 3 bytes of `abc`, whose result is an array,
Fold's recursion of depth 1000, and the Euler solver on a grid of 4 by 4 cells, whose result is the
array that `Demos.Euler.Buffered.solve 4` packs, together with the CIC decimation filter of
`TestSupport.A64.Cic` on its table of 64 samples, whose result is the array of its 8 outputs.  Each
program's arm64 Image is `genImage` of the program at `imageBase`, with the stack's room `room` and
the memory's cap `cap`.
-/

namespace TestSupport.A64

open LeanExe.A64

/-- The bytes of the stack below `main`'s frame from which `main` sets the stack's limit. -/
def room : UInt64 := 0x80000

/-- The cap of every program's memory in pages: the 16 pages that the modules of
`verified_compile` declare. -/
def cap : Nat := 16

/-- The address at which QEMU's virt machine places an arm64 Image whose `text_offset` is 0. -/
def imageBase : UInt64 := 0x40200000

/-- A program: its name, its module, the function it calls with its arguments, the form of the
result, the bytes it must write, and the status with which it must end: 0 when `main` returns
after the bytes, or the code of a trap when it reaches the exit word, which it must do with no
bytes, as Talos's run of the entry traps. -/
structure Program where
  name : String
  module : Wasm.Module
  entry : Nat
  args : List UInt64
  output : Output
  bytes : List UInt8
  status : Nat := 0

/-- The program's image at `imageBase`: its bytes and its layout. -/
def Program.image (p : Program) : Except String (List UInt8 × Layout) :=
  genImage p.module p.entry p.args room cap p.output imageBase

def programs : List Program := [
  { name := "gcd", module := TestSupport.Native.Gcd.loopCompiled.module, entry := 2
    args := [1071, 462], output := .word
    bytes := LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462) },
  { name := "gcdrec", module := TestSupport.Native.Gcd.recCompiled.module, entry := 3
    args := [1071, 462], output := .word
    bytes := LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462) },
  { name := "crc32", module := TestSupport.Bare.crcCompiled.module, entry := 5
    args := [0x3837363534333231, 0x39], output := .word
    bytes := LeanExe.Native.encodeWord (TestSupport.Bare.crcCheck 0x3837363534333231 0x39) },
  { name := "sha256", module := TestSupport.Bare.shaCompiled.module, entry := 11
    args := [0x636261], output := .array
    bytes := LeanExe.Native.encodeArray (TestSupport.Bare.shaCheck 0x636261) },
  { name := "depth", module := Verified.Examples.Fold.compiled.module, entry := 13
    args := [1000], output := .word, bytes := [], status := 1 },
  { name := "euler", module := Demos.Euler.Verified.compiled.module, entry := 28
    args := [4], output := .array
    bytes := LeanExe.Native.encodeArray (Demos.Euler.Buffered.solve 4) },
  { name := "cic", module := TestSupport.A64.Cic.compiled.module, entry := 7
    args := [64], output := .array
    bytes := LeanExe.Native.encodeArray (TestSupport.A64.Cic.cicCheck 64) }]

end TestSupport.A64
