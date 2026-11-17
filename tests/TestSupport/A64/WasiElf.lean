import Verified.Examples.WasiReadAll
import Verified.Examples.WasiPrestat
import LeanExe.A64.Wasi

/-!
The readAll command of `Verified.Examples.WasiReadAll` and the prestat command of
`Verified.Examples.WasiPrestat` as native executables for AArch64 Linux: `readAllElf` and
`prestatElf` are the files that `genWasiElf` writes for their modules, with `_start` at the index
that the compiler gives it, a memory's cap of `wasiCap` pages, and a stack of `wasiRoom` bytes.
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

/-- The index of `_start` in the prestat command's module. -/
def prestatStart : Nat :=
  Wrappers.effectIndexWith Verified.Examples.WasiPrestat.command.sysCalls
    Verified.Examples.WasiPrestat.command.pure.module 1

/-- The executable of the prestat command. -/
def prestatElf : Except String (List UInt8 × ElfLayout) :=
  genWasiElf Verified.Examples.WasiPrestat.command.module prestatStart wasiRoom wasiCap

end TestSupport.A64.WasiElf
