import Project.Drone.ExecutionHeap

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

/-- A live array that this call may read but does not release. This also covers
    the host's input array, whose allocation header has raw-buffer kind. -/
structure BorrowedWords (heap : Heap) (store : Store Unit) (node : FreeNode)
    (words : Array UInt64) : Prop where
  rootBound : 48 ≤ node.root.toNat
  capacity : 8 * (words.size + 1) ≤ node.capacity.toNat
  values : UInt64Array.At store node.root words
  below : node.root.toNat + node.capacity.toNat ≤ heap.top.toNat
  separated : ∀ other ∈ heap.nodes, regionsDisjoint node.region other.region

theorem borrow_owned {heap : Heap} {store : Store Unit} {node : FreeNode}
    {words : Array UInt64} (h : heap.OwnsWords store node words) :
    BorrowedWords heap store node words :=
  ⟨h.buffer.rootBound, h.buffer.capacity, h.buffer.values, h.below, h.separated⟩

theorem BorrowedWords.arrayAllocated {heap : Heap} {store : Store Unit} {source : FreeNode}
    {words : Array UInt64} (h : BorrowedWords heap store source words)
    (need stride : UInt64) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    BorrowedWords (heap.allocate need) (heap.allocateArrayStore store need stride) source words := by
  refine ⟨h.rootBound, h.capacity,
    h.values.frame (heap.allocateArrayStore_pages_ge store need stride) ?_, ?_, ?_⟩
  · intro address hLow hHigh
    exact arrayAllocated_bytes_in_region store heap.top need stride source heap.nodes
      h.rootBound hHeap.freeList h.separated h.below hBump address
      (by omega) (by have := h.capacity; omega)
  · have hTop := allocatedTop_toNat heap.top need heap.nodes hBump
    have hGrowth : heap.top.toNat ≤ (allocatedTop heap.top need heap.nodes).toNat := by
      rw [hTop]
      split <;> omega
    exact h.below.trans hGrowth
  · intro node hNode
    exact h.separated node (allocatedNodes_mem need heap.nodes node hNode)

theorem BorrowedWords.writesRange {heap : Heap} {initial final : Store Unit} {source : FreeNode}
    {words : Array UInt64} {start stop : Nat} (h : BorrowedWords heap initial source words)
    (hWrites : Memory.WritesRange initial final start stop)
    (hSep : source.root.toNat + source.capacity.toNat ≤ start ∨ stop ≤ source.root.toNat - 48) :
    BorrowedWords heap final source words := by
  refine ⟨h.rootBound, h.capacity, h.values.writesRange hWrites ?_, h.below, h.separated⟩
  have := h.capacity
  omega

theorem BorrowedWords.released {heap : Heap} {store : Store Unit} {source : FreeNode}
    {words : Array UInt64} (h : BorrowedWords heap store source words) (node : FreeNode)
    (hRoot : 48 ≤ node.root.toNat) (hRoot32 : node.root.toNat ≤ 4294967296)
    (hSep : regionsDisjoint source.region node.region) :
    BorrowedWords (heap.release node) (heap.releaseStore store node) source words := by
  refine ⟨h.rootBound, h.capacity, h.values.frame (Nat.le_refl _) ?_, h.below, ?_⟩
  · intro address hLow hHigh
    have hSourceRoot := h.rootBound
    have hCapacity := h.capacity
    simp only [regionsDisjoint, FreeNode.region] at hSep
    exact releasedStore_bytes store node.root (freeHead heap.nodes) heap.releases heap.frees
      hRoot hRoot32 address (by omega)
  · intro other hOther
    rcases List.mem_cons.mp hOther with rfl | hOther
    · exact hSep
    · exact h.separated other hOther

#print axioms borrow_owned
#print axioms BorrowedWords.arrayAllocated
#print axioms BorrowedWords.writesRange
#print axioms BorrowedWords.released
end Project.Drone.Execution
