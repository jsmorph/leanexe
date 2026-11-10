import Verified.Wasi.ReadCost

/-! The charge of `readAll limit`: the allocation of its buffer of `limit + 4,096` bytes, or
nothing for a limit that returns errno 61 before any allocation. -/

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

def readAllCost (limit : UInt64) : Nat :=
  if limit.toNat < 4294963200 then Bytes.allocationCost (limit.toNat + 4096) else 0

theorem readAll_capacity_toNat {limit : UInt64} (small : limit.toNat < 4294963200) :
    (limit + 4096).toNat = limit.toNat + 4096 := by
  simp only [UInt64.toNat_add, UInt64.reduceToNat]
  omega

theorem readAllCost_overflow {limit : UInt64} (large : ¬limit.toNat < 4294963200) :
    readAllCost limit = 0 := by
  simp only [readAllCost, large, ↓reduceIte]

theorem readAllCost_positive {limit : UInt64} (small : limit.toNat < 4294963200) :
    readAllCost limit = allocCost (allocSize (limit + 4096)).toNat := by
  have hCapacity := readAll_capacity_toNat small
  rw [readAllCost, ite_eq_left small, ← hCapacity,
    Bytes.allocationCost_eq (by omega) (by omega)]

theorem readAll_room_of_budget {heap : Heap} {store : Store Unit} {m : Module}
    {limit : UInt64} (small : limit.toNat < 4294963200)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBudget : heap.Within store m (readAllCost limit)) :
    heap.Room store m (allocSize (limit + 4096)) := by
  rw [readAllCost_positive small] at hBudget
  exact hBudget.room hCap

end Verified.Wasi
