import Project.EulerRiemann.FrozenHeapState
import Project.EulerRiemann.FrozenMemoryFrame

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime

theorem allocated_pages_bound (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (pageLimit : Nat) (hPages : store.mem.pages ≤ pageLimit)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ pageLimit * 65536) :
    (allocatedStore store base need nodes).mem.pages ≤ pageLimit := by
  unfold allocatedStore
  split
  · simpa only [fitStore_pages] using hPages
  · rw [bumpStore_pages]
    apply max_le hPages
    have hFit := hBump ‹_›
    unfold bumpPages
    omega

theorem Heap.allocateStore_pages_bound (heap : Heap) (store : Store Unit) (need : UInt64)
    (pageLimit : Nat) (hPages : store.mem.pages ≤ pageLimit)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ pageLimit * 65536) :
    (heap.allocateStore store need).mem.pages ≤ pageLimit :=
  allocated_pages_bound store heap.top need heap.nodes pageLimit hPages hBump

theorem allocated_grid_pages_bound (heap : Heap) (initial final : Store Unit)
    (need root : UInt64) (size pageLimit : Nat) (hPages : initial.mem.pages ≤ pageLimit)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ pageLimit * 65536)
    (hWrites : Memory.WritesGrid (heap.allocateStore initial need) final root size) :
    final.mem.pages ≤ pageLimit := by
  rw [hWrites.2.1]
  exact heap.allocateStore_pages_bound initial need pageLimit hPages hBump

#print axioms allocated_pages_bound
#print axioms Heap.allocateStore_pages_bound
#print axioms allocated_grid_pages_bound

end Project.EulerRiemann.Frozen.Execution
