import Project.EulerRiemann.OwnedWords

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.Clob Project.ProofKit

theorem Heap.finishWords (heap : Heap) (initial final : Store Unit) (need : UInt64)
    (words : Array UInt64) (hHeap : heap.At initial)
    (hNeed : 8 * (words.size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hWrites : ProofKit.Memory.WritesRange (heap.allocateArrayStore initial need 1) final
      (allocatedRoot heap.top need heap.nodes).toNat
      ((allocatedRoot heap.top need heap.nodes).toNat + 8 * (words.size + 1)))
    (hWords : UInt64Array.At final (allocatedRoot heap.top need heap.nodes) words) :
    (heap.allocate need).At final ∧
      (heap.allocate need).OwnsWords final (allocatedNode heap.top need heap.nodes) words := by
  let node := allocatedNode heap.top need heap.nodes
  let allocated := heap.allocateArrayStore initial need 1
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun hNone => (hBump hNone).le
  have hAllocatedHeap := heap.allocateArrayStore_at initial need 1 hHeap hFit
  have hBounds := allocated_bounds initial heap.top need heap.nodes hHeap.freeList hFit
  have hCapacity : 8 * (words.size + 1) ≤ node.capacity.toNat :=
    hNeed.trans (allocated_capacity need heap.nodes)
  have hRoot : 48 ≤ node.root.toNat := hBounds.1
  have hStrict : node.root.toNat + node.capacity.toNat < 4294967296 :=
    allocated_strict_bound initial heap.top need heap.nodes hHeap.freeList hBump
  have hMemory : node.root.toNat + node.capacity.toNat ≤ allocated.mem.pages * 65536 := by
    change node.root.toNat + node.capacity.toNat ≤
      (FixedArrayAllocate.allocated initial heap.top need 1 heap.nodes).mem.pages * 65536
    rw [arrayAllocated_pages]
    exact hBounds.2.2
  have hFresh : FreshFixedArrayAt allocated node.root node.capacity 1 :=
    arrayAllocated_fresh initial heap.top need 1 heap.nodes hHeap.freeList hFit
  have hSeparated := allocated_node_separated initial heap.top need heap.nodes
    hHeap.freeList hHeap.below hFit
  change ProofKit.Memory.WritesRange allocated final node.root.toNat
    (node.root.toNat + 8 * (words.size + 1)) at hWrites
  have hFinalHeap : (heap.allocate need).At final := by
    refine ⟨?_, ?_, hAllocatedHeap.below⟩
    · rw [hWrites.1]
      exact hAllocatedHeap.globals
    · apply FreeListMemory.frame_headers hAllocatedHeap.freeList hWrites.2.1.ge
      intro other hOther address hLow hHigh
      have hOtherRoot := (hAllocatedHeap.freeList.mem_bounds hOther).1
      have hSep := hSeparated other hOther
      change regionsDisjoint node.region other.region at hSep
      simp only [regionsDisjoint, FreeNode.region] at hSep
      exact hWrites.2.2 address (by omega)
  refine ⟨hFinalHeap, ⟨⟨hRoot, hCapacity, hStrict, ?_, ?_, hWords⟩, ?_, hSeparated⟩⟩
  · rw [hWrites.2.1]
    exact hMemory
  · apply hFresh.frame (by omega) hRoot (Nat.le_refl node.root.toNat)
    intro address hHigh
    exact hWrites.2.2 address (Or.inl hHigh)
  · exact (allocated_below_top heap.top need heap.nodes hHeap.below hFit).1

#print axioms Heap.finishWords
end Project.EulerRiemann.Execution
