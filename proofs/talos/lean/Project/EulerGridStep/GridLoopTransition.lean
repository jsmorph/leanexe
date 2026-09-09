import Project.EulerGridStep.GridLoopStorage
import Project.EulerGridStep.GridLoopModel

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

theorem gridLoopRoot_advance (base index : Nat) (ratio : UInt64) (input output : Array UInt64)
    (hSize : 0 < output.size) (hStatus : output[0]! = 0) :
    gridLoopRoot base (Model.advanceAt ratio input output index).size (index + 1)
      (Model.advanceAt ratio input output index)[0]! =
      arenaAdvanceRoot base output.size index (Model.cellAt ratio input index).status := by
  rw [advanceAt_size, advanceAt_header ratio input output index hSize hStatus]
  by_cases h : (Model.cellAt ratio input index).status = 0
  · simp [gridLoopRoot, arenaAdvanceRoot, h, Nat.add_assoc]
  · simp [gridLoopRoot, arenaAdvanceRoot, h]

theorem gridLoopStorage_of_advance {current : Store Unit} {base cells index : Nat}
    {ratio allocs releases frees : UInt64} {input output : Array UInt64}
    (hSize : 0 < output.size) (hStatus : output[0]! = 0)
    (hArena : ArenaAdvanceState current base cells index (Model.advanceAt ratio input output index)
      (Model.cellAt ratio input index).status allocs releases frees) :
    ∃ nextAllocs nextReleases nextFrees,
      GridLoopStorage current base cells (index + 1) (Model.advanceAt ratio input output index)
        nextAllocs nextReleases nextFrees := by
  have hHeader := advanceAt_header ratio input output index hSize hStatus
  by_cases h : (Model.cellAt ratio input index).status = 0
  · refine ⟨allocs + 6, releases + 5, frees + 5, .accepted _ _ _ _ _ (by omega) ?_ ?_⟩
    · simpa only [h, ite_true] using hHeader
    · simpa only [ArenaAdvanceState, h, ite_true] using hArena
  · refine ⟨allocs + 1, releases, frees, .rejected _ _ _ _ _ (by omega) ?_⟩
    simpa only [ArenaAdvanceState, h, ite_false, Nat.add_sub_cancel] using hArena

#print axioms gridLoopRoot_advance
#print axioms gridLoopStorage_of_advance
end Project.EulerGridStep.Execution
