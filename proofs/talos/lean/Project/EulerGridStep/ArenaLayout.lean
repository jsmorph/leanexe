import Project.EulerGridStep.ObjectFrame

namespace Project.EulerGridStep.Execution
open Wasm

/-- Forty-eight metadata bytes followed by the scalar-array length and payload. -/
def arenaObjectSize (count : Nat) : Nat := 48 + 8 * (count + 1)

def arenaHeap (base count slot : Nat) : UInt64 := UInt64.ofNat (base + slot * arenaObjectSize count)
def arenaRoot (base count slot : Nat) : UInt64 := UInt64.ofNat (base + slot * arenaObjectSize count + 48)

theorem arena_slot_fit (base count slot bound : Nat) (hSlot : slot ≤ 6)
    (hBudget : base + 7 * arenaObjectSize count ≤ bound) :
    base + slot * arenaObjectSize count + 48 + 8 * (count + 1) ≤ bound := by
  have hMul := Nat.mul_le_mul_right (arenaObjectSize count) (by omega : slot + 1 ≤ 7)
  simp only [Nat.add_mul, Nat.one_mul] at hMul
  unfold arenaObjectSize at *
  omega

theorem arena_heap_toNat (base count slot : Nat) (hSlot : slot ≤ 7)
    (hBudget : base + 7 * arenaObjectSize count ≤ 4294967296) :
    (arenaHeap base count slot).toNat = base + slot * arenaObjectSize count := by
  apply UInt64.toNat_ofNat_of_lt'
  have hMul := Nat.mul_le_mul_right (arenaObjectSize count) hSlot
  change base + slot * arenaObjectSize count < 18446744073709551616
  omega

theorem arena_root_toNat (base count slot : Nat) (hSlot : slot ≤ 6)
    (hBudget : base + 7 * arenaObjectSize count ≤ 4294967296) :
    (arenaRoot base count slot).toNat = base + slot * arenaObjectSize count + 48 := by
  apply UInt64.toNat_ofNat_of_lt'
  have hFit := arena_slot_fit base count slot 4294967296 hSlot hBudget
  change base + slot * arenaObjectSize count + 48 < 18446744073709551616
  omega

theorem arena_root_eq_heap (base count slot : Nat) :
    arenaRoot base count slot = arenaHeap base count slot + 48 := by
  simp [arenaRoot, arenaHeap, UInt64.ofNat_add]

theorem arena_heap_succ (base count slot : Nat) :
    arenaHeap base count (slot + 1) = arenaHeap base count slot + 48 + fieldRequest count := by
  change UInt64.ofNat (base + (slot + 1) * arenaObjectSize count) =
    UInt64.ofNat (base + slot * arenaObjectSize count) + UInt64.ofNat 48 + UInt64.ofNat (8 * (count + 1))
  rw [← UInt64.ofNat_add, ← UInt64.ofNat_add]
  congr 1
  simp only [Nat.add_mul, Nat.one_mul, arenaObjectSize]
  omega

/-- Every distinct pair of the seven output slots is disjoint including metadata. -/
theorem arena_roots_separate (base count a b : Nat) (ha : a ≤ 6) (hb : b ≤ 6) (hne : a ≠ b)
    (hBudget : base + 7 * arenaObjectSize count ≤ 4294967296) :
    ObjectsSeparate (arenaRoot base count a) count (arenaRoot base count b) count := by
  rw [ObjectsSeparate, arena_root_toNat base count a ha hBudget,
    arena_root_toNat base count b hb hBudget]
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

theorem arena_grid_object_size (cells : Nat) : arenaObjectSize (1 + 6 * cells) = 64 + 48 * cells := by
  unfold arenaObjectSize
  omega

#print axioms arena_slot_fit
#print axioms arena_heap_toNat
#print axioms arena_root_toNat
#print axioms arena_root_eq_heap
#print axioms arena_heap_succ
#print axioms arena_roots_separate
#print axioms arena_grid_object_size
end Project.EulerGridStep.Execution
