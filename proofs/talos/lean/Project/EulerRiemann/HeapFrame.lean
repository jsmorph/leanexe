import Project.EulerRiemann.OwnedWords

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit

structure Heap.Protects (heap : Heap) (lower upper : Nat) : Prop where
  below : upper ≤ heap.top.toNat
  separated : ∀ node ∈ heap.nodes,
    upper ≤ node.root.toNat - 48 ∨ node.root.toNat + node.capacity.toNat ≤ lower

structure Heap.Frame (before : Heap) (initial : Store Unit)
    (after : Heap) (final : Store Unit) : Prop where
  pages : initial.mem.pages ≤ final.mem.pages
  protects : ∀ lower upper, before.Protects lower upper → after.Protects lower upper
  bytes : ∀ lower upper, before.Protects lower upper → ∀ address,
    lower ≤ address → address < upper → final.mem.bytes address = initial.mem.bytes address

theorem Heap.Frame.refl (heap : Heap) (store : Store Unit) : heap.Frame store heap store :=
  ⟨Nat.le_refl _, fun _ _ h => h, fun _ _ _ _ _ _ => rfl⟩

theorem Heap.Frame.trans {first second third : Heap} {initial middle final : Store Unit}
    (h₁ : first.Frame initial second middle) (h₂ : second.Frame middle third final) :
    first.Frame initial third final := by
  refine ⟨h₁.pages.trans h₂.pages, fun lo hi h => h₂.protects lo hi (h₁.protects lo hi h), ?_⟩
  intro lo hi h address hLo hHi
  exact (h₂.bytes lo hi (h₁.protects lo hi h) address hLo hHi).trans
    (h₁.bytes lo hi h address hLo hHi)

theorem Heap.OwnsWords.protects {heap : Heap} {store : Store Unit} {node : FreeNode}
    {words : Array UInt64} (h : heap.OwnsWords store node words) :
    heap.Protects (node.root.toNat - 48) (node.root.toNat + node.capacity.toNat) := by
  refine ⟨h.below, ?_⟩
  intro other hOther
  have hSep := h.separated other hOther
  have hRoot := h.buffer.rootBound
  simp only [regionsDisjoint, FreeNode.region] at hSep
  omega

theorem Heap.Frame.ownsWords {before after : Heap} {initial final : Store Unit}
    (h : before.Frame initial after final) (hHeap : after.At final)
    {node : FreeNode} {words : Array UInt64}
    (hOwner : before.OwnsWords initial node words) : after.OwnsWords final node words := by
  have hProtected := h.protects _ _ hOwner.protects
  refine ⟨hOwner.buffer.frame_region h.pages (h.bytes _ _ hOwner.protects), hProtected.below, ?_⟩
  intro other hOther
  have hSep := hProtected.separated other hOther
  have hRoot := hOwner.buffer.rootBound
  have hOtherRoot := (hHeap.freeList.mem_bounds hOther).1
  simp only [regionsDisjoint, FreeNode.region]
  omega

theorem Heap.Frame.words {before after : Heap} {initial final : Store Unit}
    (h : before.Frame initial after final) {ptr : UInt64} {words : Array UInt64}
    (hProtected : before.Protects ptr.toNat (ptr.toNat + 8*(words.size+1)))
    (hWords : UInt64Array.At initial ptr words) : UInt64Array.At final ptr words :=
  hWords.frame h.pages (h.bytes _ _ hProtected)

theorem Heap.Protects.allocated_disjoint {heap : Heap} {lower upper : Nat}
    (h : heap.Protects lower upper) (need : UInt64)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    upper ≤ (allocatedRoot heap.top need heap.nodes).toNat - 48 ∨
      (allocatedRoot heap.top need heap.nodes).toNat + (allocatedCapacity need heap.nodes).toNat ≤ lower := by
  cases hTake : takeFirstFitFrom 0 need heap.nodes with
  | some choice =>
    simpa only [allocatedRoot, allocatedCapacity, hTake] using
      h.separated choice.node (takeFirstFitFrom_some_mem hTake)
  | none =>
    have hRoot := Allocation.root_toNat heap.top (by have := hBump hTake; omega)
    simp only [allocatedRoot, allocatedCapacity, hTake, hRoot]
    exact Or.inl (by have := h.below; omega)

theorem Heap.frame_allocate (heap : Heap) (initial : Store Unit) (need stride : UInt64)
    (hHeap : heap.At initial)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    heap.Frame initial (heap.allocate need) (heap.allocateArrayStore initial need stride) := by
  refine ⟨heap.allocateArrayStore_pages_ge initial need stride, ?_, ?_⟩
  · intro lo hi h
    refine ⟨?_, fun node hNode => h.separated node (allocatedNodes_mem need heap.nodes node hNode)⟩
    have hTop := allocatedTop_toNat heap.top need heap.nodes hBump
    change hi ≤ (allocatedTop heap.top need heap.nodes).toNat
    rw [hTop]
    split <;> have := h.below <;> omega
  · intro lo hi h address hLo hHi
    change (FixedArrayAllocate.allocated initial heap.top need stride heap.nodes).mem.bytes address = _
    cases hTake : takeFirstFitFrom 0 need heap.nodes with
    | some choice =>
      simp only [FixedArrayAllocate.allocated, hTake]
      exact FreeListMemory.fit_bytes stride lo hi address hHeap.freeList hTake h.separated hLo hHi
    | none =>
      simp only [FixedArrayAllocate.allocated, hTake]
      exact arrayBump_bytes_outside initial heap.top need stride (hBump hTake) address
        (Or.inl (by have := h.below; omega))

theorem Heap.frame_arrayWritten (heap : Heap) (initial final : Store Unit)
    (need stride : UInt64) (count : Nat) (hHeap : heap.At initial)
    (hNeed : 8*(count+1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296)
    (hWrites : ProofKit.Memory.WritesRange (heap.allocateArrayStore initial need stride) final
      (allocatedRoot heap.top need heap.nodes).toNat
      ((allocatedRoot heap.top need heap.nodes).toNat + 8*(count+1))) :
    heap.Frame initial (heap.allocate need) final := by
  have hAlloc := heap.frame_allocate initial need stride hHeap hBump
  refine ⟨hAlloc.pages.trans hWrites.2.1.ge, hAlloc.protects, ?_⟩
  intro lo hi h address hLo hHi
  have hSep := h.allocated_disjoint need hBump
  have hCapacity := allocated_capacity need heap.nodes
  exact (hWrites.2.2 address (by omega)).trans (hAlloc.bytes lo hi h address hLo hHi)

theorem Heap.Frame.released {before after : Heap} {initial final : Store Unit}
    (h : before.Frame initial after final) (node : FreeNode)
    (hRoot : 48 ≤ node.root.toNat) (hRoot32 : node.root.toNat ≤ 4294967296)
    (hSep : ∀ lo hi, before.Protects lo hi →
      hi ≤ node.root.toNat - 48 ∨ node.root.toNat + node.capacity.toNat ≤ lo) :
    before.Frame initial (after.release node) (after.releaseStore final node) := by
  refine ⟨h.pages, ?_, ?_⟩
  · intro lo hi hProtected
    have hAfter := h.protects lo hi hProtected
    refine ⟨hAfter.below, ?_⟩
    intro other hOther
    rcases List.mem_cons.mp hOther with rfl | hOther
    · exact hSep lo hi hProtected
    · exact hAfter.separated other hOther
  · intro lo hi hProtected address hLo hHi
    have hDisjoint := hSep lo hi hProtected
    exact (releasedStore_bytes final node.root (freeHead after.nodes) after.releases after.frees
      hRoot hRoot32 address (by omega)).trans (h.bytes lo hi hProtected address hLo hHi)

#print axioms Heap.Frame.trans
#print axioms Heap.Frame.ownsWords
#print axioms Heap.Frame.words
#print axioms Heap.Protects.allocated_disjoint
#print axioms Heap.frame_allocate
#print axioms Heap.frame_arrayWritten
#print axioms Heap.Frame.released
end Project.EulerRiemann.Execution
