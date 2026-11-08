import Demos.Euler.VerifiedCall
import LeanExe.A64.Proof.ProgramRuns
import LeanExe.Native.Bare

/-!
The theorem of the Euler solver's bare-metal program for AArch64, in the form `ProgramRuns`, for
every cap and every room that holds the stack's bound: `main` calls entry 28 of
`Demos.Euler.Verified.compiled.module`, the buffered solver `Demos.Euler.Buffered.solve`, on a grid
of 4 by 4 cells.  The result is a pointer to the array that the solver packs, and the machine writes
the array's length word and its elements, `encodeArray (Demos.Euler.Buffered.solve 4)`, to the
UART and returns 0.  `compiled.solve.trapFree` excludes the trap at `unreachable`, since the
solver's allocations, at most `solveBytes 4` bytes by `solve_bound`, fit the module's initial
pages, and a room of at least `stackBound`'s bytes excludes an overflow of the stack.
-/

namespace TestSupport.A64.Euler

open LeanExe.A64 Demos.Euler.Verified

/-- The heap's `top` at the module's start, plus the allocations of `solve 4`, fits the initial
pages of the memory of `compiled.module`. -/
theorem heap_room : (Verified.initialHeap compiled.tables).top.toNat + compiled.solve.bound 4 ≤
    65536 * initialPages compiled.module :=
  Nat.le_trans (Nat.add_le_add_left (solve_bound 4) _) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The theorem of the Euler solver's program. -/
theorem runs (room : UInt64) (cap : Nat) (hroom : stackBound compiled.module 28 ≤ room.toNat) :
    ProgramRuns compiled.module 28 [4] room cap .array
      (LeanExe.Native.encodeArray (Demos.Euler.Buffered.solve 4)) fun _ => False :=
  program_runs_bounded compiled.solve.trapFree 4 compiled.initial.1
    (fun hp => room_initStore heap_room hp) writes_array (.inr hroom)

end TestSupport.A64.Euler
