import Verified.Examples.WasiReadAll
import Verified.Examples.WasiClockRandom
import LeanExe.A64.Wasi

/-!
The commands of `Verified.Examples.WasiReadAll` and `Verified.Examples.WasiClockRandom` as native
executables for AArch64 Linux: `readAllElf` and `clockRandomElf` are the files that `genWasiElf`
writes for their modules, with `_start` at the index that the compiler gives it, a memory's cap of
`wasiCap` pages, and a stack of `wasiRoom` bytes.  `moduleElf` writes the executable of any module
with an export `_start`, with the same stack and a given cap.
-/

namespace TestSupport.A64.WasiElf

open LeanExe LeanExe.A64 Verified.Wasi

/-- The memory's cap of the executable, 4,096 pages. -/
def wasiCap : Nat := 4096

/-- The stack's room below `main`'s frame. -/
def wasiRoom : UInt64 := 65536

/-- The index of `_start` in the readAll command's module. -/
def readAllStart : Nat :=
  Wrappers.effectIndex Verified.Examples.WasiReadAll.command.pure.module 2

/-- The executable of the readAll command. -/
def readAllElf : Except String (List UInt8 × ElfLayout) :=
  genWasiElf Verified.Examples.WasiReadAll.command.module readAllStart wasiRoom wasiCap

/-- The index of `_start` in the clock and random command's module. -/
def clockRandomStart : Nat :=
  Wrappers.effectIndexWith Verified.Examples.WasiClockRandom.command.sysCalls
    Verified.Examples.WasiClockRandom.command.pure.module 1

/-- The executable of the clock and random command. -/
def clockRandomElf : Except String (List UInt8 × ElfLayout) :=
  genWasiElf Verified.Examples.WasiClockRandom.command.module clockRandomStart wasiRoom wasiCap

/-- The executable of the module `m`, whose export `_start` names the function to run, with a
memory's cap of `cap` pages. -/
def moduleElf (m : Wasm.Module) (cap : Nat) : Except String (List UInt8 × ElfLayout) :=
  match m.exports.find? (·.name = "_start") with
  | some e => genWasiElf m e.funcIdx wasiRoom cap
  | none => throw "no export _start"

end TestSupport.A64.WasiElf
