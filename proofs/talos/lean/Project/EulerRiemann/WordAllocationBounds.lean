import Project.EulerRiemann.OwnedWords

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit

theorem Heap.allocate_word_bounds (heap : Heap) (store : Store Unit) (need stride : UInt64) (size : Nat)
    (hHeap : heap.At store) (hNeed : 8 * (size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    (allocatedRoot heap.top need heap.nodes).toNat + 8 * (size + 1) ≤ 4294967296 ∧
    (allocatedRoot heap.top need heap.nodes).toNat + 8 * (size + 1) ≤
      (heap.allocateArrayStore store need stride).mem.pages * 65536 := by
  have hBounds := allocated_bounds store heap.top need heap.nodes hHeap.freeList hBump
  have hCapacity := allocated_capacity need heap.nodes
  constructor
  · omega
  · change (allocatedRoot heap.top need heap.nodes).toNat + 8 * (size + 1) ≤
      (FixedArrayAllocate.allocated store heap.top need stride heap.nodes).mem.pages * 65536
    rw [arrayAllocated_pages]
    omega

theorem Heap.OwnsWords.allocate_word_disjoint {heap : Heap} {store : Store Unit} {source : FreeNode}
    {words : Array UInt64} (hOwner : heap.OwnsWords store source words)
    (need : UInt64) (size : Nat) (hNeed : 8 * (size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    source.root.toNat + 8 * (words.size + 1) ≤ (allocatedRoot heap.top need heap.nodes).toNat ∨
    (allocatedRoot heap.top need heap.nodes).toNat + 8 * (size + 1) ≤ source.root.toNat := by
  have hSep := allocated_region_disjoint heap.top need source heap.nodes
    hOwner.buffer.rootBound hOwner.separated hOwner.below hBump
  have hSourceCapacity := hOwner.buffer.capacity
  have hCapacity := allocated_capacity need heap.nodes
  simp only [allocatedNode, regionsDisjoint, FreeNode.region] at hSep
  omega

theorem Heap.OwnsWords.arrayWritten {heap : Heap} {initial final : Store Unit} {source : FreeNode}
    {words : Array UInt64} (hOwner : heap.OwnsWords initial source words)
    (need stride : UInt64) (size : Nat) (hHeap : heap.At initial)
    (hNeed : 8 * (size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296)
    (hWrites : ProofKit.Memory.WritesRange (heap.allocateArrayStore initial need stride) final
      (allocatedRoot heap.top need heap.nodes).toNat
      ((allocatedRoot heap.top need heap.nodes).toNat + 8 * (size + 1))) :
    (heap.allocate need).OwnsWords final source words := by
  have hSep := allocated_region_disjoint heap.top need source heap.nodes
    hOwner.buffer.rootBound hOwner.separated hOwner.below hBump
  have hCapacity := allocated_capacity need heap.nodes
  apply (hOwner.arrayAllocated need stride hHeap hBump).writesRange hWrites
  simp only [allocatedNode, regionsDisjoint, FreeNode.region] at hSep
  omega

theorem Heap.Owns.arrayWritten {heap : Heap} {initial final : Store Unit} {source : FreeNode}
    {grid : Array Traversal.Cell} (hOwner : heap.Owns initial source grid)
    (need stride : UInt64) (size : Nat) (hHeap : heap.At initial)
    (hNeed : 8 * (size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296)
    (hWrites : ProofKit.Memory.WritesRange (heap.allocateArrayStore initial need stride) final
      (allocatedRoot heap.top need heap.nodes).toNat
      ((allocatedRoot heap.top need heap.nodes).toNat + 8 * (size + 1))) :
    (heap.allocate need).Owns final source grid := by
  have hSep := allocated_region_disjoint heap.top need source heap.nodes
    hOwner.buffer.rootBound hOwner.separated hOwner.below hBump
  have hCapacity := allocated_capacity need heap.nodes
  apply (hOwner.arrayAllocated need stride hHeap hBump).writesRange hWrites
  simp only [allocatedNode, regionsDisjoint, FreeNode.region] at hSep
  omega

#print axioms Heap.allocate_word_bounds
#print axioms Heap.OwnsWords.allocate_word_disjoint
#print axioms Heap.OwnsWords.arrayWritten
#print axioms Heap.Owns.arrayWritten

end Project.EulerRiemann.Execution
