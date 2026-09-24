import Project.ClobDepth.Heap

namespace Project.ClobDepth.HeapProof
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.EulerRiemann.Execution

structure AllocatedResult (initial : Store Unit) (heap : Heap) (need : UInt64)
    (final : Store Unit) (levels : List LevelL) : Prop where
  heapAt : (heap.allocate need).At final
  pages : final.mem.pages = initial.mem.pages
  frame : heap.Frame initial (heap.allocate need) final
  owned : OwnsLevels (heap.allocate need) final (allocatedNode heap.top need heap.nodes) levels

/-- Reconstruct an owned result and the heap frame from allocation followed
by writes confined to the result's flat data region. -/
theorem allocated_result (initial final : Store Unit) (heap : Heap) (need : UInt64)
    (levels : List LevelL) (hHeap : heap.At initial)
    (hNeed : fixedArrayBytes levels.length 2 ≤ need.toNat)
    (hBump32 : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ initial.mem.pages * 65536)
    (hPages : final.mem.pages = (heap.allocateArrayStore initial need 2).mem.pages)
    (hGlobals : final.globals.globals = (heap.allocateArrayStore initial need 2).globals.globals)
    (hOwned : OwnedLevelArrayAt final (allocatedRoot heap.top need heap.nodes)
      (allocatedCapacity need heap.nodes) levels)
    (hOutside : MemEqOutsideFlatWords (heap.allocateArrayStore initial need 2) final
      (allocatedRoot heap.top need heap.nodes) (levels.length * 2)) :
    AllocatedResult initial heap need final levels := by
  have hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun h => (hBump32 h).le
  have hAllocated := heap.allocateArrayStore_at initial need 2 hHeap hBump
  have hBounds := allocated_bounds initial heap.top need heap.nodes hHeap.freeList hBump
  have hStrict := allocated_strict_bound initial heap.top need heap.nodes hHeap.freeList hBump32
  have hCapacity := allocated_capacity need heap.nodes
  have hBelow := allocated_below_top heap.top need heap.nodes hHeap.below hBump
  have hSep := allocated_node_separated initial heap.top need heap.nodes
    hHeap.freeList hHeap.below hBump
  have hPages' := allocated_pages_eq heap initial need 2 hFit
  have hNodePages : (allocatedStore initial heap.top need heap.nodes).mem.pages =
      (heap.allocateArrayStore initial need 2).mem.pages :=
    (arrayAllocated_pages initial heap.top need 2 heap.nodes).symm
  have hFinal : (heap.allocate need).At final := by
    apply heap_written hAllocated hPages hGlobals hBounds.1 hSep
    intro address hAddress
    apply hOutside address
    unfold fixedArrayBytes at hNeed
    exact hAddress.imp id (by dsimp only [allocatedNode] at *; omega)
  refine ⟨hFinal, hPages.trans hPages', ?_, ?_⟩
  · have hFrame := heap.frame_allocate initial need 2 hHeap hBump
    refine ⟨by rw [hPages]; exact hFrame.pages, hFrame.protects, ?_⟩
    intro lo hi hProtected address hLo hHi
    have hDisjoint := hProtected.allocated_disjoint need hBump
    have hWritten : final.mem.bytes address =
        (heap.allocateArrayStore initial need 2).mem.bytes address := by
      apply hOutside address
      unfold fixedArrayBytes at hNeed
      omega
    exact hWritten.trans (hFrame.bytes lo hi hProtected address hLo hHi)
  · refine ⟨⟨hBounds.1, hNeed.trans hCapacity, hStrict, ?_, hOwned⟩, hBelow.1, hSep⟩
    rw [hPages, ← hNodePages]
    exact hBounds.2.2

/-- The length store is part of the result's data region and cannot touch
its fresh ownership header. -/
theorem allocated_length (initial : Store Unit) (heap : Heap) (need : UInt64)
    (length : Nat) (hHeap : heap.At initial)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296)
    (hRoot32 : (allocatedRoot heap.top need heap.nodes).toNat < 4294967296) :
    let root := allocatedRoot heap.top need heap.nodes
    let allocated := heap.allocateArrayStore initial need 2
    let written := { allocated with mem := allocated.mem.write64 root.toUInt32 (UInt64.ofNat length) }
    FreshFixedArrayAt written root (allocatedCapacity need heap.nodes) 2 ∧
      written.mem.read64 root.toUInt32 = UInt64.ofNat length := by
  dsimp only
  refine ⟨?_, Project.ProofKit.Memory.read64_write64 ..⟩
  have hFresh := arrayAllocated_fresh initial heap.top need 2 heap.nodes hHeap.freeList hBump
  apply FreshFixedArrayAt.write64_data hFresh
  · exact (allocated_bounds initial heap.top need heap.nodes hHeap.freeList hBump).1
  · rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hRoot32]

#print axioms allocated_result
#print axioms allocated_length
end Project.ClobDepth.HeapProof
