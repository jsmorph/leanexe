import Project.EulerGridStep.GridLoopStorage

namespace Project.EulerGridStep.Execution
open Wasm

theorem gridLoopPool_member (base count index : Nat) (status other : UInt64)
    (hMem : other ∈ gridLoopPool base count index status) :
    ∃ slot, 0 < slot ∧ slot < index + 6 ∧ other = arenaRoot base count slot := by
  by_cases hi : index = 0
  · simp [gridLoopPool, hi] at hMem
  by_cases hOne : index = 1
  · subst index
    by_cases hs : status = 0
    · simp [gridLoopPool, hs, rotatingPool, writerPool, rotatingRoots, rotatingSlot, laterSlot] at hMem
      rcases hMem with rfl | rfl | rfl | rfl | rfl
      all_goals exact ⟨_, by decide, by decide, rfl⟩
    · simp [gridLoopPool, hs, rotatingRejectedPool] at hMem
  have hRoot : ∀ completed field, field ≤ 6 →
      ∃ slot, 0 < slot ∧ slot < index + 6 ∧
        rotatingRoots base count completed field = arenaRoot base count slot := by
    intro completed field hf
    have h := rotatingSlot_bounds (completed - 1) field hf
    exact ⟨rotatingSlot (completed - 1) field, by omega, by omega, rfl⟩
  have hWriter : ∀ completed skipped,
      other ∈ writerPool (rotatingRoots base count completed) skipped →
      ∃ slot, 0 < slot ∧ slot < index + 6 ∧ other = arenaRoot base count slot := by
    intro completed skipped hm
    obtain ⟨field, _, hf, rfl⟩ := writerPool_member _ skipped other hm
    exact hRoot completed field (by omega)
  have hReuse : ∀ completed skipped,
      other ∈ reusePool (rotatingRoots base count completed) skipped →
      ∃ slot, 0 < slot ∧ slot < index + 6 ∧ other = arenaRoot base count slot := by
    intro completed skipped hm
    simp only [reusePool, List.mem_map] at hm
    obtain ⟨field, hf, rfl⟩ := hm
    have hRange := List.mem_of_mem_drop hf
    have hField := List.mem_range.mp hRange
    exact hRoot completed (field + 1) (by omega)
  by_cases hs : status = 0
  · simp only [gridLoopPool, hi, ite_false, hs, ite_true, rotatingPool, hOne, ite_false] at hMem
    exact hReuse index 0 hMem
  · simp only [gridLoopPool, hi, ite_false, hs, rotatingRejectedPool, hOne, ite_false] at hMem
    rcases List.mem_cons.mp hMem with hRootEq | hTail
    · rw [hRootEq]
      exact hRoot (index - 1) 0 (by decide)
    · unfold rotatingPoolTail at hTail
      split at hTail
      · exact hWriter (index - 1) 1 hTail
      · exact hReuse (index - 1) 1 hTail

theorem gridLoopRoot_separate_zero (base count cells index : Nat) (status : UInt64)
    (hPositive : 0 < index) (hIndex : index ≤ cells)
    (hBudget : base + (cells + 6) * arenaObjectSize count ≤ 4294967296) :
    ObjectsSeparate (arenaRoot base count 0) count (gridLoopRoot base count index status) count := by
  simp only [gridLoopRoot, Nat.ne_of_gt hPositive, ite_false]
  by_cases hOne : index = 1
  · subst index
    by_cases hs : status = 0
    · simpa [hs, rotatingRoots, rotatingSlot, laterSlot] using
        arena_roots_separate_of_lt base count 0 6 (cells + 6) (by omega) (by omega) (by decide) hBudget
    · simpa [hs, rotatingRejectedRoot] using
        arena_roots_separate_of_lt base count 0 1 (cells + 6) (by omega) (by omega) (by decide) hBudget
  · have hEight : base + 8 * arenaObjectSize count ≤ 4294967296 := by
      have hMul := Nat.mul_le_mul_right (arenaObjectSize count) (by omega : 8 ≤ cells + 6)
      omega
    by_cases hs : status = 0
    · simpa only [hs, ite_true] using
        objectsSeparate_symm (rotatingRoots_initial_separate base count index 0 (by decide) hEight)
    · simpa only [hs, ite_false, rotatingRejectedRoot, hOne, ite_false] using
        objectsSeparate_symm (rotatingRoots_initial_separate base count (index - 1) 1 (by decide) hEight)

theorem gridLoopPool_separate_zero (base count cells index : Nat) (status : UInt64)
    (hIndex : index ≤ cells)
    (hBudget : base + (cells + 6) * arenaObjectSize count ≤ 4294967296) :
    ∀ other ∈ gridLoopPool base count index status,
      ObjectsSeparate (arenaRoot base count 0) count other count := by
  intro other hMem
  obtain ⟨slot, hPositive, hSlot, rfl⟩ := gridLoopPool_member base count index status other hMem
  exact arena_roots_separate_of_lt base count 0 slot (cells + 6)
    (by omega) (by omega) (by omega) hBudget

#print axioms gridLoopPool_member
#print axioms gridLoopRoot_separate_zero
#print axioms gridLoopPool_separate_zero
end Project.EulerGridStep.Execution
