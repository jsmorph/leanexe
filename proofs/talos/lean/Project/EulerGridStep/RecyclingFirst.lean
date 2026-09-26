import Project.EulerGridStep.RecyclingTransition
import Project.EulerGridStep.RecyclingStateFacts

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

/-- The first cell retains the captured initial owner; only its intermediates are released. -/
theorem recycling_first_transition {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64)
    (hInput : UInt64Array.At initial pointer input) (hPositive : 0 < input.size / 3)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hZeroFill : output = Array.replicate output.size 0)
    (hBuffers : BufferState initial output.size [⟨arenaRoot base output.size 0, output⟩]
      [] allocs releases frees)
    (hHeap : initial.globals.globals[0]? = some (.i64 (arenaHeap base output.size 1)))
    (hBudget : base + (input.size / 3 + 6) * arenaObjectSize output.size ≤ initial.mem.pages * 65536)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 0, .i64 (arenaRoot base output.size 0), .i64 unused, .i64 pointer, .i64 inputUnused, .i64 ratio]
      (RecyclingAdvancePost m env base pointer ratio (arenaRoot base output.size 0) input output 0) := by
  have hPages := hBuffers.pages
  have hBudget32 : base + (input.size / 3 + 6) * arenaObjectSize output.size ≤ 4294967296 := by omega
  by_cases hAccepted : (Model.cellAt ratio input 0).status = 0
  · have hRoots := arena_roots_separate_of_lt base output.size 6 0 (input.size / 3 + 6)
      (by omega) (by omega) (by decide) hBudget32
    apply (advanceAt_first_preserved layout env initial ratio inputUnused pointer unused allocs releases frees
      base input output hInput hPositive hAccepted hSize hBuffers hHeap hBudget hSeparate).mono
    rintro final values ⟨hv, hArena, _, hin, hold, hInitial⟩
    refine ⟨arenaRoot base output.size 6, hv, (by
      apply liveBuffer_root_nonzero (buffer := ⟨arenaRoot base output.size 6, Model.advanceAt ratio input output 0⟩) (count := output.size)
      simpa only [advanceAt_size] using
        hArena.buffers.liveAt ⟨arenaRoot base (Model.advanceAt ratio input output 0).size 6, Model.advanceAt ratio input output 0⟩ (by simp)), (objectsSeparate_ne hRoots).symm,
      objectsSeparate_ne hRoots, hold, fun _ => ?_, fun h => False.elim (h rfl)⟩
    refine ⟨?_, hin, ?_⟩
    · simpa only [advanceAt_size] using recycling_first_accepted_state (pointer := pointer) hPositive hArena
    · simpa only [← hZeroFill] using hInitial
  · have hRoots := arena_roots_separate_of_lt base output.size 1 0 (input.size / 3 + 6)
      (by omega) (by omega) (by decide) hBudget32
    apply (advanceAt_first_rejected_preserved layout env initial ratio inputUnused pointer unused allocs releases frees
      base input output hInput hPositive hAccepted hSize hBuffers hHeap hBudget hSeparate).mono
    rintro final values ⟨hv, hArena, _, hin, hold, hInitial⟩
    refine ⟨arenaRoot base output.size 1, hv, (by
      apply liveBuffer_root_nonzero (buffer := ⟨arenaRoot base output.size 1, Model.advanceAt ratio input output 0⟩) (count := output.size)
      simpa only [advanceAt_size] using
        hArena.buffers.liveAt ⟨arenaRoot base (Model.advanceAt ratio input output 0).size 1, Model.advanceAt ratio input output 0⟩ (by simp)), (objectsSeparate_ne hRoots).symm,
      objectsSeparate_ne hRoots, hold, fun _ => ?_, fun h => False.elim (h rfl)⟩
    refine ⟨?_, hin, ?_⟩
    · have hStopped := recycling_stopped_of_buffers (pointer := pointer) (input := input) (index := 1)
        hArena.buffers (by simpa only [advanceAt_size] using hRoots)
        (by rw [hArena.status]; decide)
      simpa only [advanceAt_size] using hStopped
    · simpa only [← hZeroFill] using hInitial

#print axioms recycling_first_transition
end Project.EulerGridStep.Execution
