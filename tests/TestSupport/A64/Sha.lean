import TestSupport.Bare.Programs
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare
import Verified.Bare

/-!
The theorem of SHA-256's bare-metal program for AArch64, in the form `ProgramRuns`, for every room
of at least 5280 bytes and every cap: `main` calls entry 11 of `shaCompiled.module`, the wrapper
`shaCheck`, on the word of `abc`, and the wrapper calls `shaMsg` with the round constants.  The
result is a pointer to an array of the digest's four words.  The machine writes the array's length
word and its elements, `encodeArray (shaCheck 0x636261)`, to the UART and returns 0.  The
compiler's theorem without a trap excludes the status 1 of `unreachable`, which the allocator
reaches when the memory cannot grow, and the room of at least `stackBound`, 5280 bytes, excludes
the status 4 of an overflow of the stack.
-/

namespace TestSupport.A64.Sha

open LeanExe.A64 TestSupport.Bare

/-- The heap's `top` at the end of the tables, at byte 4616, plus the allocations of
`shaCheck 0x636261`, 544 bytes, fits the initial pages of the memory of `shaCompiled.module`. -/
theorem heap_room : (Verified.initialHeap shaCompiled.tables).top.toNat +
    shaCompiled.shaCheck.bound 0x636261 ≤ 65536 * initialPages shaCompiled.module := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The theorem of SHA-256's program.  `shaCompiled.shaCheck.trapFree` excludes the trap at
`unreachable`, since the allocations fit the memory and the table is a borrowed array of the
module's initial store.  `stackBound` gives at most 5280 bytes, which the room holds, so the stack
does not overflow. -/
theorem runs (room : UInt64) (cap : Nat) (hroom : 5280 ≤ room.toNat) :
    ProgramRuns shaCompiled.module 11 [0x636261] room cap .array
      (LeanExe.Native.encodeArray (shaCheck 0x636261)) fun _ => False :=
  program_runs_bounded shaCompiled.shaCheck.trapFree.implementsA 0x636261 shaCompiled.initial.1
    (fun hp => ⟨room_initStore heap_room hp, List.forall_mem_singleton.mpr
      (Verified.borrowed_nativeStore (shaCompiled.initial.2.2 0 (by decide)) cap)⟩)
    writes_array (.inr (Nat.le_trans (by decide +kernel) hroom))

end TestSupport.A64.Sha
