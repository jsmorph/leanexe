import Project.EulerRiemann.HeapReserve

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FreeListCount

theorem Heap.Reserved.bump_small_bound {heap : Heap} {need request : UInt64} {spare limit : Nat}
    (h : heap.Reserved need spare limit) (hSpare : 0 < spare) (hSize : request ≤ need)
    (hNone : takeFirstFitFrom 0 request heap.nodes = none) :
    heap.top.toNat + 48 + request.toNat ≤ limit := by
  have hSmallCount := fittingCount_none 0 request heap.nodes hNone
  have hCount : fittingCount need heap.nodes = 0 :=
    Nat.eq_zero_of_le_zero (hSmallCount ▸ fittingCount_mono hSize heap.nodes)
  have hSizeNat := UInt64.le_iff_toNat_le.mp hSize
  simp only [Heap.Reserved, hCount, Nat.sub_zero] at h
  nlinarith

theorem Heap.Reserved.allocate_small {heap : Heap} {need request : UInt64} {spare limit : Nat}
    (h : heap.Reserved need spare limit) (hSpare : 0 < spare) (hSize : request ≤ need)
    (hLimit : limit ≤ 4294967296) :
    (heap.allocate request).Reserved need (spare - 1) limit := by
  have hBump : takeFirstFitFrom 0 request heap.nodes = none →
      heap.top.toNat + 48 + request.toNat ≤ 4294967296 :=
    fun hNone => (h.bump_small_bound hSpare hSize hNone).trans hLimit
  have hTop := allocatedTop_toNat heap.top request heap.nodes hBump
  cases hTake : takeFirstFitFrom 0 request heap.nodes with
  | some choice =>
    have hCount := fittingCount_choice 0 request need heap.nodes choice hTake
    have hDifference : spare - 1 - fittingCount need choice.remaining ≤
        spare - fittingCount need heap.nodes := by
      split at hCount <;> omega
    simp only [Heap.Reserved, Heap.allocate, allocatedTop, allocatedNodes, hTake]
    exact (Nat.add_le_add_left
      (Nat.mul_le_mul_right (48 + need.toNat) hDifference) _).trans h
  | none =>
    have hSmallCount := fittingCount_none 0 request heap.nodes hTake
    have hCount : fittingCount need heap.nodes = 0 :=
      Nat.eq_zero_of_le_zero (hSmallCount ▸ fittingCount_mono hSize heap.nodes)
    have hSizeNat := UInt64.le_iff_toNat_le.mp hSize
    simp only [hTake, ite_true] at hTop
    simp only [Heap.Reserved, Heap.allocate, allocatedNodes, hTake, hTop, hCount, Nat.sub_zero]
    simp only [Heap.Reserved, hCount, Nat.sub_zero] at h
    have hSubtract : spare - 1 + 1 = spare := by omega
    nlinarith

#print axioms Heap.Reserved.bump_small_bound
#print axioms Heap.Reserved.allocate_small

end Project.EulerRiemann.Execution
