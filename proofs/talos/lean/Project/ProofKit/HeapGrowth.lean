import Project.EulerRiemann.HeapState

namespace Project.EulerRiemann.Execution
open Project.Runtime

theorem Heap.allocate_top_le (heap : Heap) (need : UInt64) :
    (heap.allocate need).top.toNat ≤ heap.top.toNat + 48 + need.toNat := by
  unfold Heap.allocate allocatedTop
  split
  · change heap.top.toNat ≤ heap.top.toNat + 48 + need.toNat
    omega
  · simp only [UInt64.toNat_add]
    exact (Nat.mod_le _ _).trans
      (Nat.add_le_add_right (Nat.mod_le _ _) _)

@[simp] theorem Heap.release_top (heap : Heap) (node : FreeNode) :
    (heap.release node).top = heap.top := rfl

#print axioms Heap.allocate_top_le

end Project.EulerRiemann.Execution
