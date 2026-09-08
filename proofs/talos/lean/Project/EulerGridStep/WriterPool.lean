import Project.EulerGridStep.CellPrefixes

namespace Project.EulerGridStep.Execution
open Wasm

def writerPool (roots : Nat → UInt64) (count : Nat) : List UInt64 :=
  [roots 1, roots 2, roots 3, roots 4, roots 5].drop count

theorem writerPool_head (roots : Nat → UInt64) (count : Nat) (h : count < 5) :
    writerPool roots count = roots (count + 1) :: writerPool roots (count + 1) := by
  interval_cases count <;> rfl

theorem writerPool_release (roots : Nat → UInt64) (count : Nat) (hLo : 1 ≤ count) (hHi : count ≤ 5) :
    roots count :: writerPool roots count = writerPool roots (count - 1) := by
  simpa only [Nat.sub_add_cancel hLo] using (writerPool_head roots (count - 1) (by omega)).symm

theorem writerPool_member (roots : Nat → UInt64) (count : Nat) (other : UInt64)
    (hMem : other ∈ writerPool roots count) : ∃ k, count < k ∧ k ≤ 5 ∧ other = roots k := by
  by_cases hCount : count < 5
  · interval_cases count
    · simp [writerPool] at hMem
      rcases hMem with rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, by decide, by decide, rfl⟩
      · exact ⟨2, by decide, by decide, rfl⟩
      · exact ⟨3, by decide, by decide, rfl⟩
      · exact ⟨4, by decide, by decide, rfl⟩
      · exact ⟨5, by decide, by decide, rfl⟩
    · simp [writerPool] at hMem
      rcases hMem with rfl | rfl | rfl | rfl
      · exact ⟨2, by decide, by decide, rfl⟩
      · exact ⟨3, by decide, by decide, rfl⟩
      · exact ⟨4, by decide, by decide, rfl⟩
      · exact ⟨5, by decide, by decide, rfl⟩
    · simp [writerPool] at hMem
      rcases hMem with rfl | rfl | rfl
      · exact ⟨3, by decide, by decide, rfl⟩
      · exact ⟨4, by decide, by decide, rfl⟩
      · exact ⟨5, by decide, by decide, rfl⟩
    · simp [writerPool] at hMem
      rcases hMem with rfl | rfl
      · exact ⟨4, by decide, by decide, rfl⟩
      · exact ⟨5, by decide, by decide, rfl⟩
    · simp [writerPool] at hMem
      exact ⟨5, by decide, by decide, hMem⟩
  · have hEmpty : writerPool roots count = [] := by
      apply List.drop_eq_nil_of_le
      change 5 ≤ count
      omega
    rw [hEmpty] at hMem
    contradiction

/-- Any earlier slot is separate from every node still in the five-buffer pool. -/
theorem writerPool_separate (roots : Nat → UInt64) (size slot count : Nat)
    (hSlot : slot ≤ count) (hCount : count ≤ 5)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) size (roots b) size) :
    ∀ other ∈ writerPool roots count, ObjectsSeparate (roots slot) size other size := by
  intro other hOther
  obtain ⟨k, hk, hFive, rfl⟩ := writerPool_member roots count other hOther
  exact hSlots slot (by omega) k (by omega) (by omega)

#print axioms writerPool_head
#print axioms writerPool_release
#print axioms writerPool_member
#print axioms writerPool_separate
end Project.EulerGridStep.Execution
