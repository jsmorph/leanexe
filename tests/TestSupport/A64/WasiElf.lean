import Verified.Examples.WasiReadAll
import LeanExe.A64.Wasi

/-!
The readAll command of `Verified.Examples.WasiReadAll` as a native executable for AArch64 Linux:
`readAllElf` is the file that `genWasiElf` writes for its module, with `_start` at the index that
the compiler gives it, a memory's cap of `wasiCap` pages, and a stack of `wasiRoom` bytes.
-/

namespace TestSupport.A64.WasiElf

open LeanExe LeanExe.A64 Verified.Wasi Verified.Examples.WasiReadAll

/-- The memory's cap of the executable, 4,096 pages. -/
def wasiCap : Nat := 4096

/-- The stack's room below `main`'s frame. -/
def wasiRoom : UInt64 := 65536

/-- The index of `_start` in the module. -/
def readAllStart : Nat := Wrappers.effectIndex command.pure.module 2

/-- The executable of the readAll command. -/
def readAllElf : Except String (List UInt8 × ElfLayout) :=
  genWasiElf command.module readAllStart wasiRoom wasiCap

end TestSupport.A64.WasiElf
