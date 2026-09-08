import Project.EulerGridStep.ArenaLayout

namespace Project.EulerGridStep.Execution
open Wasm

theorem arena_slot_fit_of_lt (base count slot total bound : Nat) (hSlot : slot < total)
    (hBudget : base + total * arenaObjectSize count ≤ bound) :
    base + slot * arenaObjectSize count + 48 + 8 * (count + 1) ≤ bound := by
  have hMul := Nat.mul_le_mul_right (arenaObjectSize count) (by omega : slot + 1 ≤ total)
  simp only [Nat.add_mul, Nat.one_mul] at hMul
  unfold arenaObjectSize at *
  omega

theorem arena_heap_toNat_of_le (base count slot total : Nat) (hSlot : slot ≤ total)
    (hBudget : base + total * arenaObjectSize count ≤ 4294967296) :
    (arenaHeap base count slot).toNat = base + slot * arenaObjectSize count := by
  apply UInt64.toNat_ofNat_of_lt'
  have hMul := Nat.mul_le_mul_right (arenaObjectSize count) hSlot
  change base + slot * arenaObjectSize count < 18446744073709551616
  omega

theorem arena_root_toNat_of_lt (base count slot total : Nat) (hSlot : slot < total)
    (hBudget : base + total * arenaObjectSize count ≤ 4294967296) :
    (arenaRoot base count slot).toNat = base + slot * arenaObjectSize count + 48 := by
  apply UInt64.toNat_ofNat_of_lt'
  have hFit := arena_slot_fit_of_lt base count slot total 4294967296 hSlot hBudget
  change base + slot * arenaObjectSize count + 48 < 18446744073709551616
  omega

/-- Every distinct pair of bounded output slots is disjoint including metadata. -/
theorem arena_roots_separate_of_lt (base count a b total : Nat) (ha : a < total) (hb : b < total) (hne : a ≠ b)
    (hBudget : base + total * arenaObjectSize count ≤ 4294967296) :
    ObjectsSeparate (arenaRoot base count a) count (arenaRoot base count b) count := by
  rw [ObjectsSeparate, arena_root_toNat_of_lt base count a total ha hBudget,
    arena_root_toNat_of_lt base count b total hb hBudget]
  simp only [Nat.add_sub_cancel]
  by_cases hab : a < b
  · left
    have hMul := Nat.mul_le_mul_right (arenaObjectSize count) (by omega : a + 1 ≤ b)
    simp only [Nat.add_mul, Nat.one_mul] at hMul
    unfold arenaObjectSize at *
    omega
  · right
    have hMul := Nat.mul_le_mul_right (arenaObjectSize count) (by omega : b + 1 ≤ a)
    simp only [Nat.add_mul, Nat.one_mul] at hMul
    unfold arenaObjectSize at *
    omega

#print axioms arena_slot_fit_of_lt
#print axioms arena_heap_toNat_of_le
#print axioms arena_root_toNat_of_lt
#print axioms arena_roots_separate_of_lt
end Project.EulerGridStep.Execution
