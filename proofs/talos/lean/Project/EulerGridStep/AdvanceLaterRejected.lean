import Project.EulerGridStep.RejectedBuffers
import Project.EulerGridStep.RejectedArenaState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- A rejected later cell consumes slot one, retaining four free nodes and the existing heap. -/
theorem advanceAt_later_rejected_arena {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hPositive : 0 < index) (hi : index < input.size / 3)
    (hRejected : (Model.cellAt ratio input index).status ≠ 0)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hState : LaterArenaState initial base (input.size / 3) index output allocs releases frees)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (arenaRoot base output.size (index + 5)), .i64 unused,
        .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values => values = [.i64 (arenaRoot base output.size 1), .i64 (arenaRoot base output.size 1)] ∧
        RejectedArenaState final base (input.size / 3) index (Model.advanceAt ratio input output index)
          (allocs + 1) releases frees ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input) := by
  have hBudget := hState.budget
  have hPagesBound := hState.buffers.pages
  have hBudget32 : base + (input.size / 3 + 6) * arenaObjectSize output.size ≤ 4294967296 := by omega
  have hSource := arena_roots_separate_of_lt base output.size 1 (index + 5) (input.size / 3 + 6)
    (by omega) (by omega) (by omega) hBudget32
  have hFree : ∀ other ∈ writerPool (arenaRoot base output.size) 1,
      ObjectsSeparate (arenaRoot base output.size 1) output.size other output.size := by
    intro other hOther
    obtain ⟨k, hk, hFive, rfl⟩ := writerPool_member (arenaRoot base output.size) 1 other hOther
    exact arena_roots_separate_of_lt base output.size 1 k (input.size / 3 + 6)
      (by omega) (by omega) (by omega) hBudget32
  have hCall := advanceAt_rejected_reuse_buffers layout env initial ratio inputUnused pointer unused
    (arenaRoot base output.size (index + 5)) (arenaRoot base output.size 1) allocs releases frees input output index
    (writerPool (arenaRoot base output.size) 1) hInput hi hRejected (by omega)
    (by simpa only [writerPool_head (arenaRoot base output.size) 0 (by decide)] using hState.buffers)
    hSource hFree (hSeparate 1 (by omega))
  apply hCall.mono
  rintro final values ⟨hValues, hBuffers, hHeap, hPages, _, hInputFinal⟩
  have hKeep := hBuffers.restrict_live
    [⟨arenaRoot base output.size 1, Model.advanceAt ratio input output index⟩]
    (by intro buffer hb; obtain rfl := List.mem_singleton.mp hb; exact List.mem_cons_self)
  refine ⟨hValues, ⟨?_, ?_, ?_, advanceAt_rejected_status ratio input output index hRejected (by omega)⟩,
    hPages, hInputFinal⟩
  · simpa only [advanceAt_size, rejectedPool, Nat.ne_of_gt hPositive, ite_false] using hKeep
  · simpa only [advanceAt_size, rejectedHeapSlot, Nat.ne_of_gt hPositive, ite_false] using hHeap.trans hState.heap
  · simpa only [advanceAt_size, hPages] using hBudget

#print axioms advanceAt_later_rejected_arena
end Project.EulerGridStep.Execution
