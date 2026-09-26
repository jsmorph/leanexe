import Project.EulerGridStep.RotatingArenaState
import Project.EulerGridStep.AdvanceMixedProtected
import Project.EulerGridStep.AdvanceReusedProtected

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

theorem advanceAt_rotating_accepted {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hPositive : 0 < index) (hi : index < input.size / 3)
    (hAccepted : (Model.cellAt ratio input index).status = 0)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hState : RotatingArenaState initial base (input.size / 3) index output allocs releases frees)
    (initialOutput : Array UInt64)
    (hProtected : (⟨arenaRoot base output.size 0, initialOutput⟩ : LiveBuffer).At initial output.size)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (rotatingRoots base output.size index 0), .i64 unused,
        .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values =>
        values = [.i64 (rotatingRoots base output.size index 6), .i64 (rotatingRoots base output.size index 6)] ∧
        BufferState final output.size
          [⟨rotatingRoots base output.size index 6, Model.advanceAt ratio input output index⟩,
            ⟨rotatingRoots base output.size index 0, output⟩]
          (writerPool (rotatingRoots base output.size index) 0)
          (allocs + 6) (releases + 5) (frees + 5) ∧
        final.globals.globals[0]? = some (.i64 (arenaHeap base output.size 8)) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input ∧
        (⟨arenaRoot base output.size 0, initialOutput⟩ : LiveBuffer).At final output.size) := by
  have hBudget := hState.eight_slot_bound hPositive hi
  have hSlots := rotatingRoots_separate base output.size index hBudget
  have hInputSeparate : ∀ field ≤ 6,
      ObjectsSeparate (rotatingRoots base output.size index field) output.size pointer input.size := by
    intro field hField
    have hBound := rotatingSlot_bounds (index - 1) field hField
    exact hSeparate _ (by omega)
  have hInitialSeparate : ∀ field, 1 ≤ field → field ≤ 6 →
      ObjectsSeparate (rotatingRoots base output.size index field) output.size
        (arenaRoot base output.size 0) output.size := by
    intro field _ hField
    exact rotatingRoots_initial_separate base output.size index field hField hBudget
  by_cases hFirst : index = 1
  · subst index
    have hCall := advanceAt_mixed_protected layout env initial ratio inputUnused pointer unused
      (arenaHeap base output.size 7) allocs releases frees (rotatingRoots base output.size 1)
      input output 1 hInput hi hAccepted (by omega) (hState.mixed _ hi)
      (by simp [rotatingRoots, rotatingSlot, laterSlot, arena_root_eq_heap]) hSlots hInputSeparate
      ⟨arenaRoot base output.size 0, initialOutput⟩ hProtected hInitialSeparate
    simpa only [writerPool, List.drop_zero, ← arena_heap_succ base output.size 7] using hCall
  · have hCall := advanceAt_reused_protected layout env initial ratio inputUnused pointer unused
      (arenaHeap base output.size 8) allocs releases frees (rotatingRoots base output.size index)
      input output index hInput hi hAccepted (by omega) (hState.reused _ (by omega))
      hSlots hInputSeparate ⟨arenaRoot base output.size 0, initialOutput⟩ hProtected hInitialSeparate
    simpa only [writerPool, List.drop_zero] using hCall

#print axioms advanceAt_rotating_accepted
end Project.EulerGridStep.Execution
