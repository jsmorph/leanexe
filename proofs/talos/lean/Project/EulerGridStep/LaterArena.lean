import Project.EulerGridStep.ArenaBounds
import Project.EulerGridStep.WriterPool

namespace Project.EulerGridStep.Execution
open Wasm

/-- Earlier final outputs remain allocated; only slots one through five are reused. -/
def laterSlot (completed field : Nat) : Nat :=
  if field = 0 then completed + 5 else if field = 6 then completed + 6 else field

def laterRoots (base count completed : Nat) (field : Nat) : UInt64 :=
  arenaRoot base count (laterSlot completed field)

theorem later_slot_bound (cells completed field : Nat) (hi : completed < cells) (hf : field ≤ 6) :
    laterSlot completed field < cells + 6 := by
  unfold laterSlot
  split_ifs <;> omega

theorem later_slot_injective (completed a b : Nat) (hi : 0 < completed)
    (ha : a ≤ 6) (hb : b ≤ 6) (hne : a ≠ b) : laterSlot completed a ≠ laterSlot completed b := by
  intro hEq
  unfold laterSlot at hEq
  split_ifs at hEq <;> omega

theorem later_roots_separate (base count cells completed : Nat) (hi : 0 < completed)
    (hLoop : completed < cells) (hBudget : base + (cells + 6) * arenaObjectSize count ≤ 4294967296) :
    ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b →
      ObjectsSeparate (laterRoots base count completed a) count (laterRoots base count completed b) count := by
  intro a ha b hb hne
  exact arena_roots_separate_of_lt base count (laterSlot completed a) (laterSlot completed b) (cells + 6)
    (later_slot_bound cells completed a hLoop ha) (later_slot_bound cells completed b hLoop hb)
    (later_slot_injective completed a b hi ha hb hne) hBudget

theorem later_root_zero (base count completed : Nat) :
    laterRoots base count completed 0 = arenaRoot base count (completed + 5) := by
  simp [laterRoots, laterSlot]

theorem later_root_six (base count completed : Nat) :
    laterRoots base count completed 6 = arenaHeap base count (completed + 6) + 48 := by
  simp [laterRoots, laterSlot, arena_root_eq_heap]

theorem later_pool (base count completed : Nat) :
    writerPool (laterRoots base count completed) 0 = writerPool (arenaRoot base count) 0 := by
  simp [writerPool, laterRoots, laterSlot]

/-- One pending fresh object fits under the complete grid's explicit object budget. -/
theorem later_fresh_space (current : Store Unit) (base count cells completed : Nat)
    (hLoop : completed < cells) (hPages : current.mem.pages ≤ 65536)
    (hBudget : base + (cells + 6) * arenaObjectSize count ≤ current.mem.pages * 65536) :
    (arenaHeap base count (completed + 6)).toNat + 48 + 8 * (count + 1) ≤ current.mem.pages * 65536 := by
  have hBudget32 : base + (cells + 6) * arenaObjectSize count ≤ 4294967296 := by omega
  rw [arena_heap_toNat_of_le base count (completed + 6) (cells + 6) (by omega) hBudget32]
  exact arena_slot_fit_of_lt base count (completed + 6) (cells + 6) _ (by omega) hBudget

#print axioms later_slot_bound
#print axioms later_slot_injective
#print axioms later_roots_separate
#print axioms later_root_zero
#print axioms later_root_six
#print axioms later_pool
#print axioms later_fresh_space
end Project.EulerGridStep.Execution
