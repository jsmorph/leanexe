import TestSupport.Bare.Programs
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare
import Verified.Bare

/-!
The theorem of CRC-32's bare-metal program for AArch64, in the form `ProgramRuns`, for every room
and cap: `main` calls entry 5 of `crcCompiled.module`, the wrapper `crcCheck`, on the two words of
`123456789`, and the wrapper calls `crcMsg` with the table of CRC-32.  The machine writes the eight
bytes of `crcCheck 0x3837363534333231 0x39` to the UART and returns 0.  The compiler's theorem
without a trap excludes the status 1 of `unreachable`, which the allocator reaches when the memory
cannot grow, and `stackBound` excludes the status 4 of an overflow of the stack.
-/

namespace TestSupport.A64.Crc

open LeanExe.A64 TestSupport.Bare

/-- The heap's `top` at the end of the tables, at byte 6152, plus the allocations of
`crcCheck 0x3837363534333231 0x39`, 232 bytes, fits the initial pages of the memory of
`crcCompiled.module`. -/
theorem heap_room : (Verified.initialHeap crcCompiled.tables).top.toNat +
    crcCompiled.crcCheck.bound (0x3837363534333231, 0x39) ≤
      65536 * initialPages crcCompiled.module := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The theorem of CRC-32's program.  `crcCompiled.crcCheck.trapFree` excludes the trap at
`unreachable`, since the allocations fit the memory and the table is a borrowed array of the
module's initial store.  `stackBound` gives at most 4096 bytes, which the room holds, so the stack
does not overflow. -/
theorem runs (room : UInt64) (cap : Nat) :
    ProgramRuns crcCompiled.module 5 [0x3837363534333231, 0x39] room cap .word
      (LeanExe.Native.encodeWord (crcCheck 0x3837363534333231 0x39)) fun _ => False :=
  program_runs_bounded crcCompiled.crcCheck.trapFree.implementsA (0x3837363534333231, 0x39)
    crcCompiled.initial.1 (fun hp => ⟨room_initStore heap_room hp, List.forall_mem_singleton.mpr
      (Verified.borrowed_nativeStore (crcCompiled.initial.2.2 0 (by decide)) cap)⟩)
    writes_word (.inl (by decide +kernel))

end TestSupport.A64.Crc
