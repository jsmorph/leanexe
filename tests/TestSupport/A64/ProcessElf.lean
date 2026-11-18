import Demos.OrderBook.ProcessModule
import Demos.RunningSum.Module
import Demos.RunningSumFp.Module
import LeanExe.A64.Proof.WasiProgram
import Verified.Wasi.ProcessFacts

/-!
The three WASI process modules whose functions have frames of 4,096 bytes or more as native
executables for AArch64 Linux: the order book's process, with five such functions, and the running
sum and the floating-point running sum, with one each.  `genWasiElf` accepts each module with
`_start` at the index that the compiler gives it, a memory's cap of `procCap` pages, and a stack's
room of `procRoom` bytes (`orderbook_elf_ok`, `running_sum_elf_ok`, `running_sumfp_elf_ok`), and
the room holds each module's stack bound, the premise `hroom` of
`Verified.ShimA64.wasiElf_run` and `Verified.ShimA64.wasiElf_footprint` (`orderbook_room`,
`running_sum_room`, `running_sumfp_room`).  The kernel evaluates the generator and the bounds in
this module alone, which no root of the full check imports, and
`lake build TestSupport.A64.ProcessElf` checks it.
-/

namespace TestSupport.A64.ProcessElf

open LeanExe LeanExe.A64

/-- The memory's cap of the executables, 4,096 pages. -/
def procCap : Nat := 4096

/-- The stack's room below `main`'s frame. -/
def procRoom : UInt64 := 65536

/-- The index of the order book's `_start`. -/
def orderBookStart : Nat :=
  Verified.Wasi.ProcessEntry.startIndex Demos.OrderBook.Process.io.pure.module
    Demos.OrderBook.Process.entry

/-- The index of the running sum's `_start`. -/
def runningSumStart : Nat :=
  Verified.Wasi.ProcessEntry.startIndex Demos.RunningSum.io.pure.module Demos.RunningSum.entry

/-- The index of the floating-point running sum's `_start`. -/
def runningSumFpStart : Nat :=
  Verified.Wasi.ProcessEntry.startIndex Demos.RunningSumFp.io.pure.module
    Demos.RunningSumFp.entry

set_option maxRecDepth 100000

theorem orderbook_elf_ok :
    (genWasiElf Demos.OrderBook.Process.module orderBookStart procRoom procCap).isOk = true := by
  decide +kernel

theorem orderbook_room :
    wasiStackBound Demos.OrderBook.Process.module orderBookStart ≤ procRoom.toNat := by
  decide +kernel

theorem running_sum_elf_ok :
    (genWasiElf Demos.RunningSum.module runningSumStart procRoom procCap).isOk = true := by
  decide +kernel

theorem running_sum_room :
    wasiStackBound Demos.RunningSum.module runningSumStart ≤ procRoom.toNat := by
  decide +kernel

theorem running_sumfp_elf_ok :
    (genWasiElf Demos.RunningSumFp.module runningSumFpStart procRoom procCap).isOk = true := by
  decide +kernel

theorem running_sumfp_room :
    wasiStackBound Demos.RunningSumFp.module runningSumFpStart ≤ procRoom.toNat := by
  decide +kernel

end TestSupport.A64.ProcessElf
