import Project.EulerRiemann.ArrayAllocationMemory
import Project.EulerRiemann.HeapGrid
import Project.ProofKit.MemoryFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.Clob Project.ProofKit

theorem arrayAllocated_bytes_in_region (store : Store Unit) (base need stride : UInt64)
    (source : FreeNode) (nodes : List FreeNode) (hRoot : 48 ≤ source.root.toNat)
    (hList : FreeListAt store.mem nodes)
    (hSep : ∀ node ∈ nodes, regionsDisjoint source.region node.region)
    (hHeap : source.root.toNat + source.capacity.toNat ≤ base.toNat)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296)
    (address : Nat) (hLow : source.root.toNat - 48 ≤ address)
    (hHigh : address < source.root.toNat + source.capacity.toNat) :
    (FixedArrayAllocate.allocated store base need stride nodes).mem.bytes address =
      store.mem.bytes address := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simp only [FixedArrayAllocate.allocated, hTake]
    apply FreeListMemory.fit_bytes stride (source.root.toNat - 48)
      (source.root.toNat + source.capacity.toNat) address hList hTake ?_ hLow hHigh
    intro node hNode
    have hDisjoint := hSep node hNode
    have hNode48 := (hList.mem_bounds hNode).1
    simp only [regionsDisjoint, FreeNode.region] at hDisjoint
    omega
  | none =>
    simp only [FixedArrayAllocate.allocated, hTake]
    exact arrayBump_bytes_outside store base need stride (hBump hTake) address (Or.inl (by omega))

theorem Heap.allocateArrayStore_pages_ge (heap : Heap) (store : Store Unit) (need stride : UInt64) :
    store.mem.pages ≤ (heap.allocateArrayStore store need stride).mem.pages := by
  change store.mem.pages ≤ (FixedArrayAllocate.allocated store heap.top need stride heap.nodes).mem.pages
  rw [arrayAllocated_pages]
  exact allocated_pages_ge ..

theorem OwnedGridAt.frame_region {initial final : Store Unit} {node : FreeNode}
    {grid : Array Traversal.Cell} (h : OwnedGridAt initial node grid)
    (hPages : initial.mem.pages ≤ final.mem.pages)
    (hBytes : ∀ address : Nat,
      node.root.toNat - 48 ≤ address → address < node.root.toNat + node.capacity.toNat →
      final.mem.bytes address = initial.mem.bytes address) : OwnedGridAt final node grid := by
  refine ⟨h.rootBound, h.capacity, h.addressBound,
    h.memoryBound.trans (Nat.mul_le_mul_right 65536 hPages),
    h.fresh.frame_region (by have := h.addressBound; omega) h.rootBound ?_, ?_⟩
  · intro address hLow hHigh
    exact hBytes address hLow (by omega)
  · exact h.values.frame hPages (fun _ hLow hHigh =>
      hBytes _ (by omega) (by have := h.capacity; omega))

theorem Heap.Owns.arrayAllocated {heap : Heap} {store : Store Unit} {source : FreeNode}
    {grid : Array Traversal.Cell} (hOwner : heap.Owns store source grid)
    (need stride : UInt64) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    (heap.allocate need).Owns (heap.allocateArrayStore store need stride) source grid := by
  refine ⟨hOwner.buffer.frame_region (heap.allocateArrayStore_pages_ge store need stride)
    (arrayAllocated_bytes_in_region store heap.top need stride source heap.nodes
      hOwner.buffer.rootBound hHeap.freeList hOwner.separated hOwner.below hBump), ?_, ?_⟩
  · have hTop := allocatedTop_toNat heap.top need heap.nodes hBump
    have hGrowth : heap.top.toNat ≤ (allocatedTop heap.top need heap.nodes).toNat := by
      rw [hTop]
      split <;> omega
    exact hOwner.below.trans hGrowth
  · intro node hNode
    exact hOwner.separated node (allocatedNodes_mem need heap.nodes node hNode)

theorem Heap.Owns.writesRange {heap : Heap} {initial final : Store Unit} {source : FreeNode}
    {grid : Array Traversal.Cell} {start stop : Nat} (hOwner : heap.Owns initial source grid)
    (hWrites : ProofKit.Memory.WritesRange initial final start stop)
    (hSep : source.root.toNat + source.capacity.toNat ≤ start ∨ stop ≤ source.root.toNat - 48) :
    heap.Owns final source grid :=
  ⟨hOwner.buffer.frame_region hWrites.2.1.ge
    (fun _ hLow hHigh => hWrites.2.2 _ (by omega)), hOwner.below, hOwner.separated⟩

#print axioms arrayAllocated_bytes_in_region
#print axioms Heap.allocateArrayStore_pages_ge
#print axioms OwnedGridAt.frame_region
#print axioms Heap.Owns.arrayAllocated
#print axioms Heap.Owns.writesRange

end Project.EulerRiemann.Execution
