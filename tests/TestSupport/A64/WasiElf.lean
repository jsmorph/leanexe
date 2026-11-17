import Verified.Examples.WasiReadAll
import Verified.Examples.WasiClockRandom
import Verified.Examples.WasiSysEnviron
import TestSupport.A64.WasiArgs
import LeanExe.A64.Wasi

/-!
WASI commands as native executables for AArch64 Linux, each the file that `genWasiElf` writes for
its module, with `_start` at the index that the compiler gives it, a memory's cap of `wasiCap`
pages, and a stack of `wasiRoom` bytes: `readAllElf` of the readAll command of
`Verified.Examples.WasiReadAll`, `environElf` of the environment command of
`Verified.Examples.WasiSysEnviron`, which writes its environment, `argsElf` of the command of
`TestSupport.A64.WasiArgs`, which writes its arguments, and `clockRandomElf` of the clock and
random command of `Verified.Examples.WasiClockRandom`.  `moduleElf` writes the executable of any
module with an export `_start`, with the same stack and a given cap.
-/

namespace TestSupport.A64.WasiElf

open LeanExe LeanExe.A64 Verified.Wasi

/-- The memory's cap of the executables, 4,096 pages. -/
def wasiCap : Nat := 4096

/-- The stack's room below `main`'s frame. -/
def wasiRoom : UInt64 := 65536

open Verified.Examples.WasiReadAll in
/-- The index of `_start` in the readAll command's module. -/
def readAllStart : Nat := Wrappers.effectIndex command.pure.module 2

open Verified.Examples.WasiReadAll in
/-- The executable of the readAll command. -/
def readAllElf : Except String (List UInt8 × ElfLayout) :=
  genWasiElf command.module readAllStart wasiRoom wasiCap

open Verified.Examples.WasiClockRandom in
/-- The index of `_start` in the clock and random command's module. -/
def clockRandomStart : Nat := Wrappers.effectIndexWith command.sysCalls command.pure.module 1

open Verified.Examples.WasiClockRandom in
/-- The executable of the clock and random command. -/
def clockRandomElf : Except String (List UInt8 × ElfLayout) :=
  genWasiElf command.module clockRandomStart wasiRoom wasiCap

/-- The executable of the module `m`, whose export `_start` names the function to run, with a
memory's cap of `cap` pages. -/
def moduleElf (m : Wasm.Module) (cap : Nat) : Except String (List UInt8 × ElfLayout) :=
  match m.exports.find? (·.name = "_start") with
  | some e => genWasiElf m e.funcIdx wasiRoom cap
  | none => throw "no export _start"

open Verified.Examples.WasiSysEnviron in
/-- The index of `_start` in the environment command's module. -/
def environStart : Nat := Wrappers.effectIndexWith command.sysCalls command.pure.module 1

open Verified.Examples.WasiSysEnviron in
/-- The executable of the environment command. -/
def environElf : Except String (List UInt8 × ElfLayout) :=
  genWasiElf command.module environStart wasiRoom wasiCap

open TestSupport.A64.WasiArgs in
/-- The index of `_start` in the arguments command's module. -/
def argsStart : Nat := Wrappers.effectIndexWith command.sysCalls command.pure.module 1

open TestSupport.A64.WasiArgs in
/-- The executable of the arguments command. -/
def argsElf : Except String (List UInt8 × ElfLayout) :=
  genWasiElf command.module argsStart wasiRoom wasiCap

end TestSupport.A64.WasiElf
