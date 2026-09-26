import Project.ClobDepth.AllocationFacts

namespace Project.ClobDepth.HeapProof
open Wasm Project.Common Project.Clob Project.Runtime Project.ProofKit
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.EulerRiemann.Execution

set_option maxRecDepth 16384

def initialized (initial : Store Unit) (heap : Heap) (need : UInt64) (count : Nat) : Store Unit :=
  let allocated := heap.allocateArrayStore initial need 2
  { allocated with mem := allocated.mem.write64 (allocatedRoot heap.top need heap.nodes).toUInt32 (UInt64.ofNat count) }

structure CopyReady (initial : Store Unit) (heap : Heap) (need : UInt64)
    (count : Nat) (source : FreeNode) (levels : List LevelL) : Prop where
  pages : (initialized initial heap need count).mem.pages = initial.mem.pages
  fresh : FreshFixedArrayAt (initialized initial heap need count)
    (allocatedRoot heap.top need heap.nodes) (allocatedCapacity need heap.nodes) 2
  length : (initialized initial heap need count).mem.read64
    (allocatedRoot heap.top need heap.nodes).toUInt32 = UInt64.ofNat count
  sourceRead : LevelsAt (initialized initial heap need count) source.root levels
  rootBound : 48 ≤ (allocatedRoot heap.top need heap.nodes).toNat
  addressBound : (allocatedRoot heap.top need heap.nodes).toNat + (count * 2 + 1) * 8 < 4294967296
  memoryBound : (allocatedRoot heap.top need heap.nodes).toNat + (count * 2 + 1) * 8 ≤
    (initialized initial heap need count).mem.pages * 65536
  sourceBound : source.root.toNat + (levels.length * 2 + 1) * 8 < 4294967296
  separated : flatWordsDisjoint (flatWordsRegion (allocatedRoot heap.top need heap.nodes) (count * 2))
    (flatWordsRegion source.root (levels.length * 2))
  outside : MemEqOutsideFlatWords (heap.allocateArrayStore initial need 2)
    (initialized initial heap need count) (allocatedRoot heap.top need heap.nodes) (count * 2)

theorem initialize_copy (initial : Store Unit) (heap : Heap) (need : UInt64)
    (count : Nat) (source : FreeNode) (levels : List LevelL)
    (hHeap : heap.At initial) (hOwner : OwnsLevels heap initial source levels)
    (hNeed : fixedArrayBytes count 2 ≤ need.toNat)
    (hBump32 : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ initial.mem.pages * 65536) :
    CopyReady initial heap need count source levels := by
  have hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun h => (hBump32 h).le
  have hHeap' := heap.allocateArrayStore_at initial need 2 hHeap hBump
  have hPages := allocated_pages_eq heap initial need 2 hFit
  have hOwner' := hOwner.frame (heap.frame_allocate initial need 2 hHeap hBump) hPages hHeap'
  have hBounds := allocated_bounds initial heap.top need heap.nodes hHeap.freeList hBump
  have hStrict := allocated_strict_bound initial heap.top need heap.nodes hHeap.freeList hBump32
  have hCapacity := allocated_capacity need heap.nodes
  have hSep := allocated_region_disjoint heap.top need source heap.nodes hOwner.buffer.rootBound
    hOwner.separated hOwner.below hBump
  have hSourceCapacity := hOwner.buffer.capacity
  have hSourceBound := hOwner.buffer.addressBound
  have hAddress : (allocatedRoot heap.top need heap.nodes).toNat + (count * 2 + 1) * 8 < 4294967296 := by
    dsimp only [allocatedNode] at hStrict
    unfold fixedArrayBytes at hNeed
    omega
  have hSourceAddress : source.root.toNat + (levels.length * 2 + 1) * 8 < 4294967296 := by
    unfold fixedArrayBytes at hSourceCapacity
    omega
  have hDataSep : flatWordsDisjoint
      (flatWordsRegion (allocatedRoot heap.top need heap.nodes) (count * 2))
      (flatWordsRegion source.root (levels.length * 2)) := by
    simp only [regionsDisjoint, FreeNode.region, allocatedNode] at hSep
    simp only [flatWordsDisjoint, flatWordsRegion]
    unfold fixedArrayBytes at hNeed hSourceCapacity
    omega
  have hInitial := allocated_length initial heap need count hHeap hBump (by omega)
  refine ⟨hPages, hInitial.1, hInitial.2, ?_, hBounds.1, hAddress, ?_, hSourceAddress,
    hDataSep, ?_⟩
  · have h := LevelsAt.frame_write64_flatWordsDisjoint
      (slot := 0) (value := UInt64.ofNat count) hSourceAddress hAddress
      (Nat.zero_le _) hDataSep hOwner'.buffer.contents.2
    simpa only [initialized, toUInt32_eq_ofNat, Nat.zero_mul, Nat.add_zero] using h
  · change _ ≤ (FixedArrayAllocate.allocated initial heap.top need 2 heap.nodes).mem.pages * 65536
    rw [arrayAllocated_pages]
    unfold fixedArrayBytes at hNeed
    omega
  · have h : MemEqOutsideFlatWords (heap.allocateArrayStore initial need 2)
        (heap.allocateArrayStore initial need 2)
        (allocatedRoot heap.top need heap.nodes) (count * 2) := fun _ _ => rfl
    have hWritten := h.write64 (slot := 0) (value := UInt64.ofNat count) hAddress (Nat.zero_le _)
    simpa only [initialized, toUInt32_eq_ofNat, Nat.zero_mul, Nat.add_zero] using hWritten

#print axioms initialize_copy
end Project.ClobDepth.HeapProof
