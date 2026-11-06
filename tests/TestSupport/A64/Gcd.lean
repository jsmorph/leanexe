import TestSupport.Native.Gcd
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare

/-!
The theorems of GCD's bare-metal programs for AArch64, in the form `ProgramRuns`, for every room
and cap.  In the first, `main` calls entry 2 of `loopCompiled.module`, the loop of `gcd`, on 1071
and 462, and the machine writes the eight bytes of `gcd 1071 462` to the UART and returns 0.  In
the second, `main` calls entry 3 of `recCompiled.module`, the recursion of `gcd` with the depth of
calls, and the machine writes the same bytes and returns 0, or it reaches the exit word with the
status 4 of an overflow of the stack.  The compiler's theorem without a trap excludes the status 1
of the depth's guard, and the recursion's cycle of calls leaves the stack without a static bound.
-/

namespace TestSupport.A64.Gcd

open LeanExe.A64 TestSupport.Native.Gcd

/-- The theorem of GCD's loop: `loopCompiled.gcd.implements` excludes every trap, and the stack
that the loop uses is at most 4096 bytes. -/
theorem runs (room : UInt64) (cap : Nat) :
    ProgramRuns loopCompiled.module 2 [1071, 462] room cap .word
      (LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462)) fun _ => False :=
  program_runs_bounded loopCompiled.gcd.implements (1071, 462) loopCompiled.initial.1
    (fun _ => trivial) writes_word (.inl (by decide +kernel))

/-- The recursion of `gcd` on 1071 and 462 fits the frames of the depth's guard. -/
theorem rec_fits : recCompiled.gcd.fits 1000 (1071, 462) = true := by
  decide +kernel

/-- The heap's `top` at the end of the tables, plus the allocations of `gcd 1071 462`, fits the
initial pages of the memory of `recCompiled.module`. -/
theorem rec_heap_room : (Verified.initialHeap recCompiled.tables).top.toNat +
    recCompiled.gcd.bound 1000 (1071, 462) ≤ 65536 * initialPages recCompiled.module := by
  decide +kernel

/-- The recursion's cycle of calls leaves `stackBound` at 2^64, which bounds nothing. -/
theorem rec_stack_bound : stackBound recCompiled.module 3 = 2 ^ 64 := by
  decide +kernel

/-- The theorem of GCD's recursion: `main` calls entry 3 of `recCompiled.module`, which calls the
recursion of `gcd` with depth 0, on 1071 and 462.  `recCompiled.gcd.trapFree` excludes the trap of
the depth's guard and of the allocator: the recursion on 1071 and 462 fits the guard's frames, and
its allocations fit the memory.  The recursion's calls form a cycle, so `stackBound` bounds
nothing, and the overflow remains. -/
theorem rec_runs (room : UInt64) (cap : Nat) :
    ProgramRuns recCompiled.module 3 [1071, 462] room cap .word
      (LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462)) fun c => c = 4 :=
  program_runs_trapFree recCompiled.gcd.trapFree (1071, 462) recCompiled.initial.1
    (fun hp => ⟨rec_fits, room_initStore rec_heap_room hp⟩) writes_word

end TestSupport.A64.Gcd
