import Project.EulerGridStep.GridLoopStorage
import Project.EulerGridStep.GridLoopModel

namespace Project.EulerGridStep.Execution
open Wasm Project.ProofKit

def gridAdvanceRoot (base count index : Nat) (status : UInt64) : UInt64 :=
  if index = 0 then arenaAdvanceRoot base count 0 status
  else rotatingRoots base count index (if status = 0 then 6 else 1)

theorem gridLoopRoot_advance (base index : Nat) (ratio : UInt64) (input output : Array UInt64)
    (hSize : 0 < output.size) (hStatus : output[0]! = 0) :
    gridLoopRoot base (Model.advanceAt ratio input output index).size (index + 1)
      (Model.advanceAt ratio input output index)[0]! =
      gridAdvanceRoot base output.size index (Model.cellAt ratio input index).status := by
  rw [advanceAt_size, advanceAt_header ratio input output index hSize hStatus]
  by_cases hi : index = 0
  · subst index
    by_cases h : (Model.cellAt ratio input 0).status = 0 <;>
      simp [gridLoopRoot, gridAdvanceRoot, arenaAdvanceRoot, rotatingRoots, rotatingSlot,
        laterSlot, rotatingRejectedRoot, h]
  · by_cases h : (Model.cellAt ratio input index).status = 0
    · simp [gridLoopRoot, gridAdvanceRoot, h, hi,
        rotatingRoots_succ base output.size index 0 (by omega), rotateIndex]
    · simp [gridLoopRoot, gridAdvanceRoot, rotatingRejectedRoot, h, hi,
        show index + 1 ≠ 1 by omega]

theorem gridLoopStorage_of_first {current : Store Unit} {base cells : Nat}
    {ratio allocs releases frees : UInt64} {input output : Array UInt64}
    (hSize : 0 < output.size) (hStatus : output[0]! = 0)
    (hArena : ArenaAdvanceState current base cells 0 (Model.advanceAt ratio input output 0)
      (Model.cellAt ratio input 0).status allocs releases frees) :
    ∃ nextAllocs nextReleases nextFrees,
      GridLoopStorage current base cells 1 (Model.advanceAt ratio input output 0)
        nextAllocs nextReleases nextFrees := by
  have hHeader := advanceAt_header ratio input output 0 hSize hStatus
  by_cases h : (Model.cellAt ratio input 0).status = 0
  · refine ⟨allocs + 6, releases + 5, frees + 5, .accepted _ _ _ _ _ (by omega) ?_ ?_⟩
    · simpa only [h, ite_true] using hHeader
    · apply RotatingArenaState.of_first
      simpa only [ArenaAdvanceState, h, ite_true] using hArena
  · have ha : RejectedArenaState current base cells 0 (Model.advanceAt ratio input output 0)
        (allocs + 1) releases frees := by
      simpa only [ArenaAdvanceState, h, ite_false] using hArena
    refine ⟨allocs + 1, releases, frees, .rejected _ _ _ _ _ (by omega) ?_⟩
    exact ⟨by simpa [rotatingRejectedRoot, rotatingRejectedPool, rejectedPool] using ha.buffers,
      by simpa [rotatingRejectedHeapSlot, rejectedHeapSlot] using ha.heap, ha.budget, ha.status⟩

#print axioms gridLoopRoot_advance
#print axioms gridLoopStorage_of_first
end Project.EulerGridStep.Execution
