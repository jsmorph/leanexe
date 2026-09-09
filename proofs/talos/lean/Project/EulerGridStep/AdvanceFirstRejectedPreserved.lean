import Project.EulerGridStep.RejectedBuffers
import Project.EulerGridStep.RejectedArenaState
import Project.EulerGridStep.ArenaAllocation

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- A rejected first cell allocates only slot one, leaving an empty pool and heap slot two. -/
theorem advanceAt_first_rejected_preserved {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64)
    (hInput : UInt64Array.At initial pointer input) (hPositive : 0 < input.size / 3)
    (hRejected : (Model.cellAt ratio input 0).status ≠ 0)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hBuffers : BufferState initial output.size [⟨arenaRoot base output.size 0, output⟩]
      [] allocs releases frees)
    (hHeap : initial.globals.globals[0]? = some (.i64 (arenaHeap base output.size 1)))
    (hBudget : base + (input.size / 3 + 6) * arenaObjectSize output.size ≤ initial.mem.pages * 65536)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 0, .i64 (arenaRoot base output.size 0), .i64 unused,
        .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values => values = [.i64 (arenaRoot base output.size 1), .i64 (arenaRoot base output.size 1)] ∧
        RejectedArenaState final base (input.size / 3) 0 (Model.advanceAt ratio input output 0)
          (allocs + 1) releases frees ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input ∧
        UInt64Array.At final (arenaRoot base output.size 0) output ∧
        (⟨arenaRoot base output.size 0, output⟩ : LiveBuffer).At final output.size) := by
  have hSeven : base + 7 * arenaObjectSize output.size ≤ initial.mem.pages * 65536 := by
    have hMul := Nat.mul_le_mul_right (arenaObjectSize output.size) (by omega : 7 ≤ input.size / 3 + 6)
    omega
  have hPagesBound := hBuffers.pages
  have hBudget32 : base + 7 * arenaObjectSize output.size ≤ 4294967296 := by omega
  have hValid := arena_fresh_valid initial base output.size 1 0 allocs output rfl
    (by decide) (by decide) (by decide) hSeven hBuffers.pages hHeap
    (by simpa using hBuffers.freeHead) hBuffers.allocations
  have hCall := advanceAt_rejected_fresh_buffers layout env initial ratio inputUnused pointer unused
    (arenaRoot base output.size 0) (arenaHeap base output.size 1) allocs releases frees input output 0
    hInput hPositive hRejected (by omega) hBuffers hValid
    (by simpa only [arena_root_eq_heap] using
      arena_roots_separate base output.size 1 0 (by decide) (by decide) (by decide) hBudget32)
    (by simpa only [arena_root_eq_heap] using hSeparate 1 (by omega))
  apply hCall.mono
  rintro final values ⟨hValues, hFinalBuffers, hFinalHeap, hPages, _, hInputFinal⟩
  have hPreserved : (⟨arenaRoot base output.size 0, output⟩ : LiveBuffer).At final output.size :=
    hFinalBuffers.liveAt _ (by simp)
  have hKeep := hFinalBuffers.restrict_live
    [⟨arenaHeap base output.size 1 + 48, Model.advanceAt ratio input output 0⟩]
    (by intro buffer hb; obtain rfl := List.mem_singleton.mp hb; exact List.mem_cons_self)
  refine ⟨?_, ⟨?_, ?_, ?_, advanceAt_rejected_status ratio input output 0 hRejected (by omega)⟩,
    hPages, hInputFinal, hPreserved.2.2, hPreserved⟩
  · simpa only [arena_root_eq_heap] using hValues
  · simpa only [advanceAt_size, rejectedPool, ite_true, arena_root_eq_heap] using hKeep
  · simpa only [advanceAt_size, rejectedHeapSlot, ite_true,
      show 2 = (1 : Nat) + 1 from rfl, arena_heap_succ] using hFinalHeap
  · simpa only [advanceAt_size, hPages] using hBudget

#print axioms advanceAt_first_rejected_preserved
end Project.EulerGridStep.Execution
