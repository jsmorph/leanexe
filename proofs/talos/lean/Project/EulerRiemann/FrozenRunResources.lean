import Project.EulerRiemann.FrozenExecutionInitialCells
import Project.EulerRiemann.FrozenExecutionAdvanceTotal

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime

def runInitialBytes (n : Nat) : Nat := 112 + initialRemainingBytes 1 20 (n * n)

def runBytes (n spare : Nat) : Nat :=
  runInitialBytes n + (spare + 3) * (48 + initialBytes (n * n))

theorem gridCapacity_toNat (n : Nat) (hn : n ≤ 800) :
    (gridCapacity n).toNat = initialBytes (n * n) := by
  exact initial_requested_bytes (n * n) (by have := Nat.mul_le_mul hn hn; omega)

theorem run_advance_reservation (heap : Heap) (n spare initialLimit limit : Nat)
    (hn : n ≤ 800) (hTop : heap.top.toNat ≤ initialLimit)
    (hRoom : initialLimit + (spare + 3) * (48 + initialBytes (n * n)) ≤ limit) :
    heap.Reserved (gridCapacity n) (spare + 3) limit := by
  unfold Heap.Reserved
  calc
    _ ≤ initialLimit + (spare + 3) * (48 + initialBytes (n * n)) :=
      Nat.add_le_add hTop (by
        rw [gridCapacity_toNat n hn]
        exact Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    _ ≤ limit := hRoom

theorem run_bytes_bound (n : Nat) (hn : n ≤ 800) : runBytes n 0 ≤ 319523176 := by
  have hSize := Nat.mul_le_mul hn hn
  have hInitial := initial_remaining_bound (n * n) hSize
  simp only [runBytes, runInitialBytes, initialBytes] at ⊢
  omega

#print axioms gridCapacity_toNat
#print axioms run_advance_reservation
#print axioms run_bytes_bound

end Project.EulerRiemann.Frozen.Execution
