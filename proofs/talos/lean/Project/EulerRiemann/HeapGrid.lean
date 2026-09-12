import Project.EulerRiemann.HeapState
import Project.EulerRiemann.OwnedGrid

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

structure Heap.Owns (heap : Heap) (store : Store Unit) (node : FreeNode)
    (grid : Array Traversal.Cell) : Prop where
  buffer : OwnedGridAt store node grid
  below : node.root.toNat + node.capacity.toNat ≤ heap.top.toNat
  separated : ∀ other ∈ heap.nodes, regionsDisjoint node.region other.region

theorem Heap.Owns.allocated {heap : Heap} {store : Store Unit} {source : FreeNode}
    {grid : Array Traversal.Cell} (hOwner : heap.Owns store source grid)
    (need : UInt64) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    (heap.allocate need).Owns (heap.allocateStore store need) source grid := by
  refine ⟨(hOwner.buffer.allocated heap.top need heap.nodes hHeap.freeList
    hOwner.separated hOwner.below hBump).mem_congr rfl, ?_, ?_⟩
  · have hTop := allocatedTop_toNat heap.top need heap.nodes hBump
    have hGrowth : heap.top.toNat ≤ (allocatedTop heap.top need heap.nodes).toNat := by
      rw [hTop]
      split <;> omega
    exact hOwner.below.trans hGrowth
  · intro node hNode
    exact hOwner.separated node (allocatedNodes_mem need heap.nodes node hNode)

theorem Heap.Owns.writes {heap : Heap} {initial final : Store Unit} {source : FreeNode}
    {grid : Array Traversal.Cell} {target : UInt64} {size : Nat}
    (hOwner : heap.Owns initial source grid) (hWrites : Memory.WritesGrid initial final target size)
    (hSep : source.root.toNat + source.capacity.toNat ≤ target.toNat ∨
      target.toNat + 8 * (7 * size + 1) ≤ source.root.toNat - 48) :
    heap.Owns final source grid :=
  ⟨hOwner.buffer.writes hWrites hSep, hOwner.below, hOwner.separated⟩

theorem Heap.Owns.released {heap : Heap} {store : Store Unit} {source : FreeNode}
    {grid : Array Traversal.Cell} (hOwner : heap.Owns store source grid) (node : FreeNode)
    (hRoot : 48 ≤ node.root.toNat) (hRoot32 : node.root.toNat ≤ 4294967296)
    (hSep : regionsDisjoint source.region node.region) :
    (heap.release node).Owns (heap.releaseStore store node) source grid := by
  refine ⟨hOwner.buffer.released node (freeHead heap.nodes) heap.releases heap.frees hRoot hRoot32 hSep,
    hOwner.below, ?_⟩
  intro other hOther
  rcases List.mem_cons.mp hOther with rfl | hOther
  · exact hSep
  · exact hOwner.separated other hOther

theorem Heap.Owns.swept {heap : Heap} {initial final : Store Unit} {source : FreeNode}
    {grid : Array Traversal.Cell} (hOwner : heap.Owns initial source grid)
    (need : UInt64) (size : Nat) (hHeap : heap.At initial)
    (hNeed : 8 * (7 * size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296)
    (hWrites : Memory.WritesGrid (heap.allocateStore initial need)
      final (allocatedRoot heap.top need heap.nodes) size) :
    (heap.allocate need).Owns final source grid := by
  have hSourceRoot := hOwner.buffer.rootBound
  have hRoot := (allocated_bounds initial heap.top need heap.nodes hHeap.freeList hBump).1
  have hCapacity := allocated_capacity need heap.nodes
  have hDisjoint := allocated_region_disjoint heap.top need source heap.nodes hSourceRoot
    hOwner.separated hOwner.below hBump
  apply (hOwner.allocated need hHeap hBump).writes hWrites
  simp only [allocatedNode, regionsDisjoint, FreeNode.region] at hDisjoint
  omega

#print axioms Heap.Owns.allocated
#print axioms Heap.Owns.writes
#print axioms Heap.Owns.released
#print axioms Heap.Owns.swept

end Project.EulerRiemann.Execution
