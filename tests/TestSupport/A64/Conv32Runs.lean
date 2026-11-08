import TestSupport.A64.Conv32
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare

/-!
The theorem of the binary32 conversions' bare-metal program for AArch64, in the form `ProgramRuns`,
for every room and cap: `main` calls entry 4 of `compiled.module`, the wrapper `convCheck`, on 64,
and the machine writes the array's length word and its elements, `encodeArray (convCheck 64)`, to
the UART and returns 0.  `compiled.convCheck.trapFree` excludes the trap at `unreachable`, since
the allocations of `convCheck 64` fit the module's initial pages above the heap's `top`, and
`stackBound` lies within the 4096 bytes that every room exceeds.
-/

namespace TestSupport.A64.Conv32

open LeanExe.A64

/-- The heap's `top` at the module's start, plus the allocations of `convCheck 64`, fits the
initial pages of the memory of `compiled.module`. -/
theorem heap_room : (Verified.initialHeap compiled.tables).top.toNat +
    compiled.convCheck.bound 64 ≤ 65536 * initialPages compiled.module := by
  rw [compiled.convCheck.bound_eq, Verified.blockCost_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The theorem of the binary32 conversions' program. -/
theorem runs (room : UInt64) (cap : Nat) :
    ProgramRuns compiled.module 4 [64] room cap .array
      (LeanExe.Native.encodeArray (convCheck 64)) fun _ => False :=
  program_runs_bounded compiled.convCheck.trapFree 64 compiled.initial.1
    (fun hp => room_initStore heap_room hp) writes_array (.inl (by decide +kernel))

end TestSupport.A64.Conv32
