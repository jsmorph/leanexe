import Verified.Bytes.Allocation

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

def readCost (capacity : UInt64) : Nat :=
  if capacity.toNat < 4294967296 then Bytes.allocationCost capacity.toNat else 0

@[simp] theorem readCost_zero : readCost 0 = 0 := rfl

theorem readCost_overflow {capacity : UInt64} (h : 4294967296 ≤ capacity.toNat) :
    readCost capacity = 0 := by
  simp only [readCost, ite_eq_right (by omega : ¬capacity.toNat < 4294967296)]

theorem readCost_positive {capacity : UInt64} (hSize : capacity.toNat < 4294967296)
    (hNonzero : capacity ≠ 0) : readCost capacity = allocCost (allocSize capacity).toNat := by
  have hNat : capacity.toNat ≠ 0 := by
    intro hZero
    apply hNonzero
    apply UInt64.toNat_inj.mp
    exact hZero
  rw [readCost, ite_eq_left hSize, Bytes.allocationCost_eq hNat (Nat.le_of_lt hSize)]

theorem read_room_of_budget {heap : Heap} {store : Store Unit} {m : Module}
    {capacity : UInt64} (hSize : capacity.toNat < 4294967296) (hNonzero : capacity ≠ 0)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBudget : heap.Within store m (readCost capacity)) :
    heap.Room store m (allocSize capacity) := by
  rw [readCost_positive hSize hNonzero] at hBudget
  exact hBudget.room hCap

end Verified.Wasi
