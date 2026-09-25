import Project.EulerRiemann.FrozenArrayAllocationFrame
import Project.ProofKit.ArrayPrefix

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.Clob Project.ProofKit

structure OwnedWordsAt (store : Store Unit) (node : FreeNode) (words : Array UInt64) : Prop where
  rootBound : 48 ≤ node.root.toNat
  capacity : 8 * (words.size + 1) ≤ node.capacity.toNat
  addressBound : node.root.toNat + node.capacity.toNat < 4294967296
  memoryBound : node.root.toNat + node.capacity.toNat ≤ store.mem.pages * 65536
  fresh : FreshFixedArrayAt store node.root node.capacity 1
  values : UInt64Array.At store node.root words

theorem OwnedWordsAt.frame_region {initial final : Store Unit} {node : FreeNode}
    {words : Array UInt64} (h : OwnedWordsAt initial node words)
    (hPages : initial.mem.pages ≤ final.mem.pages)
    (hBytes : ∀ address : Nat,
      node.root.toNat - 48 ≤ address → address < node.root.toNat + node.capacity.toNat →
      final.mem.bytes address = initial.mem.bytes address) : OwnedWordsAt final node words := by
  refine ⟨h.rootBound, h.capacity, h.addressBound,
    h.memoryBound.trans (Nat.mul_le_mul_right 65536 hPages),
    h.fresh.frame_region (by have := h.addressBound; omega) h.rootBound ?_, ?_⟩
  · intro address hLow hHigh
    exact hBytes address hLow (by omega)
  · exact h.values.frame hPages (fun _ hLow hHigh =>
      hBytes _ (by omega) (by have := h.capacity; omega))

structure Heap.OwnsWords (heap : Heap) (store : Store Unit) (node : FreeNode)
    (words : Array UInt64) : Prop where
  buffer : OwnedWordsAt store node words
  below : node.root.toNat + node.capacity.toNat ≤ heap.top.toNat
  separated : ∀ other ∈ heap.nodes, regionsDisjoint node.region other.region

theorem Heap.OwnsWords.arrayAllocated {heap : Heap} {store : Store Unit} {source : FreeNode}
    {words : Array UInt64} (hOwner : heap.OwnsWords store source words)
    (need stride : UInt64) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    (heap.allocate need).OwnsWords (heap.allocateArrayStore store need stride) source words := by
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

theorem Heap.OwnsWords.writesRange {heap : Heap} {initial final : Store Unit} {source : FreeNode}
    {words : Array UInt64} {start stop : Nat} (hOwner : heap.OwnsWords initial source words)
    (hWrites : ProofKit.Memory.WritesRange initial final start stop)
    (hSep : source.root.toNat + source.capacity.toNat ≤ start ∨ stop ≤ source.root.toNat - 48) :
    heap.OwnsWords final source words :=
  ⟨hOwner.buffer.frame_region hWrites.2.1.ge
    (fun _ hLow hHigh => hWrites.2.2 _ (by omega)), hOwner.below, hOwner.separated⟩

theorem Heap.OwnsWords.released {heap : Heap} {store : Store Unit} {source : FreeNode}
    {words : Array UInt64} (hOwner : heap.OwnsWords store source words) (node : FreeNode)
    (hRoot : 48 ≤ node.root.toNat) (hRoot32 : node.root.toNat ≤ 4294967296)
    (hSep : regionsDisjoint source.region node.region) :
    (heap.release node).OwnsWords (heap.releaseStore store node) source words := by
  refine ⟨hOwner.buffer.frame_region (Nat.le_refl _) ?_, hOwner.below, ?_⟩
  · intro address hLow hHigh
    have hSourceRoot := hOwner.buffer.rootBound
    simp only [regionsDisjoint, FreeNode.region] at hSep
    exact releasedStore_bytes store node.root (freeHead heap.nodes) heap.releases heap.frees
      hRoot hRoot32 address (by omega)
  · intro other hOther
    rcases List.mem_cons.mp hOther with rfl | hOther
    · exact hSep
    · exact hOwner.separated other hOther

#print axioms OwnedWordsAt.frame_region
#print axioms Heap.OwnsWords.arrayAllocated
#print axioms Heap.OwnsWords.writesRange
#print axioms Heap.OwnsWords.released

end Project.EulerRiemann.Frozen.Execution
