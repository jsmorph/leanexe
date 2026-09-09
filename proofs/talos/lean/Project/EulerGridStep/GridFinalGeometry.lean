import Project.EulerGridStep.GridLoopStorage

namespace Project.EulerGridStep.Execution
open Wasm

theorem gridLoopPool_member (base count index : Nat) (status other : UInt64)
    (hMem : other ∈ gridLoopPool base count index status) :
    ∃ slot, 0 < slot ∧ slot ≤ 5 ∧ other = arenaRoot base count slot := by
  by_cases hi : index = 0
  · simp [gridLoopPool, hi] at hMem
  · by_cases hs : status = 0
    · simpa only [gridLoopPool, hi, ite_false, hs, ite_true] using
        (writerPool_member (arenaRoot base count) 0 other
          (by simpa only [gridLoopPool, hi, ite_false, hs, ite_true] using hMem))
    · simp only [gridLoopPool, hi, ite_false, hs, rejectedPool] at hMem
      split at hMem
      · contradiction
      · obtain ⟨slot, hOne, hFive, hRoot⟩ := writerPool_member (arenaRoot base count) 1 other hMem
        exact ⟨slot, by omega, hFive, hRoot⟩

/-- The final output is never the initial slot once a cell has run. -/
theorem gridLoopRoot_separate_zero (base count cells index : Nat) (status : UInt64)
    (hPositive : 0 < index) (hIndex : index ≤ cells)
    (hBudget : base + (cells + 6) * arenaObjectSize count ≤ 4294967296) :
    ObjectsSeparate (arenaRoot base count 0) count (gridLoopRoot base count index status) count := by
  simp only [gridLoopRoot, Nat.ne_of_gt hPositive, ite_false]
  split
  · exact arena_roots_separate_of_lt base count 0 (index + 5) (cells + 6)
      (by omega) (by omega) (by omega) hBudget
  · exact arena_roots_separate_of_lt base count 0 1 (cells + 6)
      (by omega) (by omega) (by omega) hBudget

theorem gridLoopPool_separate_zero (base count cells index : Nat) (status : UInt64)
    (hBudget : base + (cells + 6) * arenaObjectSize count ≤ 4294967296) :
    ∀ other ∈ gridLoopPool base count index status,
      ObjectsSeparate (arenaRoot base count 0) count other count := by
  intro other hMem
  obtain ⟨slot, hPositive, hFive, rfl⟩ := gridLoopPool_member base count index status other hMem
  exact arena_roots_separate_of_lt base count 0 slot (cells + 6)
    (by omega) (by omega) (by omega) hBudget

#print axioms gridLoopPool_member
#print axioms gridLoopRoot_separate_zero
#print axioms gridLoopPool_separate_zero
end Project.EulerGridStep.Execution
