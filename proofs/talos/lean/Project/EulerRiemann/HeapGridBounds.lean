import Project.EulerRiemann.HeapGrid

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

theorem Heap.allocate_grid_bounds (heap : Heap) (store : Store Unit) (need : UInt64) (size : Nat)
    (hHeap : heap.At store) (hNeed : 8 * (7 * size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    (allocatedRoot heap.top need heap.nodes).toNat + 8 * (7 * size + 1) ≤ 4294967296 ∧
    (allocatedRoot heap.top need heap.nodes).toNat + 8 * (7 * size + 1) ≤
      (heap.allocateStore store need).mem.pages * 65536 := by
  have hBounds := allocated_bounds store heap.top need heap.nodes hHeap.freeList hBump
  have hCapacity := allocated_capacity need heap.nodes
  change 48 ≤ (allocatedRoot heap.top need heap.nodes).toNat ∧
    (allocatedRoot heap.top need heap.nodes).toNat + (allocatedCapacity need heap.nodes).toNat ≤ 4294967296 ∧
    (allocatedRoot heap.top need heap.nodes).toNat + (allocatedCapacity need heap.nodes).toNat ≤
      (heap.allocateStore store need).mem.pages * 65536 at hBounds
  constructor <;> omega

theorem Heap.Owns.allocate_grid_disjoint {heap : Heap} {store : Store Unit} {source : FreeNode}
    {grid : Array Traversal.Cell} (hOwner : heap.Owns store source grid)
    (need : UInt64) (size : Nat)
    (hNeed : 8 * (7 * size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    source.root.toNat + 8 * (7 * grid.size + 1) ≤ (allocatedRoot heap.top need heap.nodes).toNat ∨
    (allocatedRoot heap.top need heap.nodes).toNat + 8 * (7 * size + 1) ≤ source.root.toNat := by
  have hDisjoint := allocated_region_disjoint heap.top need source heap.nodes
    hOwner.buffer.rootBound hOwner.separated hOwner.below hBump
  have hSourceCapacity := hOwner.buffer.capacity
  have hCapacity := allocated_capacity need heap.nodes
  simp only [allocatedNode, regionsDisjoint, FreeNode.region] at hDisjoint
  omega

#print axioms Heap.allocate_grid_bounds
#print axioms Heap.Owns.allocate_grid_disjoint

end Project.EulerRiemann.Execution
