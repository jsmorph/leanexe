import Project.EulerGridStep.GridAdvanceFinish
import Project.EulerGridStep.AdvanceRotatingAccepted

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

theorem gridLoop_advance {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hi : index < input.size / 3)
    (hSize : output.size = 1 + 6 * (input.size / 3)) (hStatus : output[0]! = 0)
    (hStorage : GridLoopStorage initial base (input.size / 3) index output allocs releases frees)
    (hProtected : (⟨arenaRoot base output.size 0, Array.replicate output.size 0⟩ : LiveBuffer).At initial output.size)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (gridLoopRoot base output.size index output[0]!), .i64 unused,
        .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values =>
        let next := Model.advanceAt ratio input output index
        values = [.i64 (gridLoopRoot base next.size (index + 1) next[0]!),
          .i64 (gridLoopRoot base next.size (index + 1) next[0]!)] ∧
        UInt64Array.At final (gridLoopRoot base output.size index output[0]!) output ∧
        GridAdvanceFinish m env final base index pointer input output next) := by
  dsimp only
  rw [gridLoopRoot_advance base index ratio input output (by omega) hStatus]
  cases hStorage with
  | initial a r f hBuffers hHeap hBudget =>
      simp only [gridLoopRoot, gridAdvanceRoot, ite_true]
      apply (advanceAt_first_preserved_outcome layout env initial ratio inputUnused pointer unused allocs releases frees base
        input (Array.replicate (1 + 6 * (input.size / 3)) 0) hInput hi hSize
        (by simpa using hBuffers) (by simpa using hHeap) (by simpa using hBudget) hSeparate).mono
      rintro final values ⟨hv, ha, hp, hg, ho, hb⟩
      refine ⟨hv, ho, ?_⟩
      simp only [GridAdvanceFinish, ite_true, GridNextState]
      exact ⟨gridLoopStorage_of_first (by simp) hStatus ha, hg,
        by simpa only [advanceAt_size, Array.size_replicate] using hb⟩
  | accepted i out a r f hPositive hs hArena =>
      simp only [gridLoopRoot, Nat.ne_of_gt hPositive, ite_false, hs, ite_true,
        gridAdvanceRoot, Nat.ne_of_gt hPositive, ite_false]
      have hEight := hArena.eight_slot_bound hPositive hi
      have hInputSeparate : ObjectsSeparate (rotatingRoots base output.size index 0) output.size pointer input.size := by
        have hBound := rotatingSlot_bounds (index - 1) 0 (by decide)
        exact hSeparate _ (by omega)
      by_cases hAccepted : (Model.cellAt ratio input index).status = 0
      · simp only [hAccepted, ite_true]
        apply (advanceAt_rotating_accepted layout env initial ratio inputUnused pointer unused allocs releases frees base
          input output index hInput hPositive hi hAccepted hSize hArena
          (Array.replicate output.size 0) hProtected hSeparate).mono
        rintro final values ⟨hv, hb, hh, hp, hg, ho⟩
        refine ⟨hv, (hb.liveAt ⟨rotatingRoots base output.size index 0, output⟩ (by simp)).2.2, ?_⟩
        apply grid_positive_finish layout env final base index ratio pointer
          (allocs + 6) (releases + 5) (frees + 5) input output hPositive (by omega) hs
          (by simpa only [gridPendingPool, hAccepted, ite_true] using hb)
          (by simpa only [gridPendingHeapSlot, hAccepted, ite_true] using hh)
          (by simpa only [hp] using hArena.budget) hEight hg hInputSeparate ho
      · simp only [hAccepted, ite_false]
        apply (advanceAt_rotating_rejected layout env initial ratio inputUnused pointer unused allocs releases frees base
          input output index hInput hPositive hi hAccepted hSize hArena
          (Array.replicate output.size 0) hProtected hSeparate).mono
        rintro final values ⟨hv, hb, hh, hp, hg, ho⟩
        refine ⟨hv, (hb.liveAt ⟨rotatingRoots base output.size index 0, output⟩ (by simp)).2.2, ?_⟩
        apply grid_positive_finish layout env final base index ratio pointer
          (allocs + 1) releases frees input output hPositive (by omega) hs
          (by simpa only [gridPendingPool, hAccepted, ite_false] using hb)
          (by simpa only [gridPendingHeapSlot, hAccepted, ite_false] using hh)
          (by simpa only [hp] using hArena.budget) hEight hg hInputSeparate ho
  | rejected i out a r f hPositive hArena =>
      have h := hStatus.symm.trans hArena.status
      exact False.elim (by simpa using h)

#print axioms gridLoop_advance
end Project.EulerGridStep.Execution
