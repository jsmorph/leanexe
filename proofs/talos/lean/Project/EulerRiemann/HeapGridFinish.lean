import Project.EulerRiemann.HeapGrid

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.Clob

theorem Heap.finishGrid (heap : Heap) (initial final : Store Unit) (need : UInt64)
    (grid : Array Traversal.Cell) (hHeap : heap.At initial)
    (hNeed : 8 * (7 * grid.size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hWrites : Memory.WritesGrid (heap.allocateStore initial need) final
      (allocatedRoot heap.top need heap.nodes) grid.size)
    (hGrid : Memory.GridAt final (allocatedRoot heap.top need heap.nodes) grid) :
    (heap.allocate need).At final ∧
      (heap.allocate need).Owns final (allocatedNode heap.top need heap.nodes) grid := by
  let node := allocatedNode heap.top need heap.nodes
  let allocated := heap.allocateStore initial need
  change Memory.WritesGrid allocated final node.root grid.size at hWrites
  change Memory.GridAt final node.root grid at hGrid
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun hNone => Nat.le_of_lt (hBump hNone)
  have hAllocatedHeap := heap.allocate_at initial need hHeap hFit
  have hBounds := allocated_bounds initial heap.top need heap.nodes hHeap.freeList hFit
  change 48 ≤ node.root.toNat ∧ node.root.toNat + node.capacity.toNat ≤ 4294967296 ∧
    node.root.toNat + node.capacity.toNat ≤ allocated.mem.pages * 65536 at hBounds
  have hCapacity : 8 * (7 * grid.size + 1) ≤ node.capacity.toNat :=
    hNeed.trans (allocated_capacity need heap.nodes)
  have hStrict : node.root.toNat + node.capacity.toNat < 4294967296 :=
    allocated_strict_bound initial heap.top need heap.nodes hHeap.freeList hBump
  have hFresh : FreshFixedArrayAt allocated node.root node.capacity 7 :=
    allocated_fresh initial heap.top need heap.nodes hHeap.freeList hFit
  have hSeparated := allocated_node_separated initial heap.top need heap.nodes
    hHeap.freeList hHeap.below hFit
  have hGridSeparated : gridFreeSeparated node.root grid.size (heap.allocate need).nodes := by
    intro other hMember
    have hOther48 := (hAllocatedHeap.freeList.mem_bounds hMember).1
    have hSeparate := hSeparated other hMember
    change regionsDisjoint node.region other.region at hSeparate
    simp only [regionsDisjoint, FreeNode.region] at hSeparate
    omega
  have hFinalHeap : (heap.allocate need).At final := by
    refine ⟨?_, hWrites.freeList hAllocatedHeap.freeList hGridSeparated, hAllocatedHeap.below⟩
    rw [hWrites.globals]
    exact hAllocatedHeap.globals
  refine ⟨hFinalHeap, ⟨⟨hBounds.1, hCapacity, hStrict, ?_,
    hWrites.fresh hBounds.1 (by omega) hFresh, hGrid⟩, ?_, hSeparated⟩⟩
  · rw [hWrites.2.1]
    exact hBounds.2.2
  · exact (allocated_below_top heap.top need heap.nodes hHeap.below hFit).1

#print axioms Heap.finishGrid

end Project.EulerRiemann.Execution
