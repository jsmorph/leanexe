import Project.LebU32.RecyclingCode
import Project.ProofKit.HeapGrowth
import Project.EulerRiemann.AllocationPageBound

namespace Project.LebU32.Recycling
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

structure Arena (initial : Store Unit) (base : UInt64) (count : Nat)
    (heap : Heap) (store : Store Unit) : Prop where
  heapAt : heap.At store
  top : heap.top.toNat ≤ base.toNat + 56 * count
  pages : store.mem.pages = initial.mem.pages
  protection : heap.Protects 0 base.toNat
  prefixBytes : ∀ address, address < base.toNat → store.mem.bytes address = initial.mem.bytes address
  cap : store.memoryCap «module» 0 = initial.memoryCap «module» 0

structure Buffer (base : UInt64) (heap : Heap) (store : Store Unit)
    (node : FreeNode) (bytes : ByteArray) : Prop where
  values : PackedMemory.ByteArrayAt store.mem node.root.toNat bytes
  protection : heap.Protects node.root.toNat (node.root.toNat + bytes.size)
  empty : bytes.size = 0 → node.root = 0
  owned : bytes.size ≠ 0 → heap.OwnsPacked store node bytes
  above : bytes.size ≠ 0 → base.toNat ≤ node.root.toNat - 48

theorem need_small (bytes : ByteArray) (hSize : bytes.size < 5) : PackedPush.need bytes = 8 := by
  apply UInt64.toNat.inj
  rw [PackedPush.need, PackedCapacity.capacity_toNat _ (by omega)]
  change max 8 (((bytes.size + 1 + 7) / 8) * 8) = 8
  omega

theorem Arena.bump {initial store : Store Unit} {base : UInt64} {count : Nat} {heap : Heap}
    (h : Arena initial base count heap store) (hCount : count < 5)
    (hFit32 : base.toNat + 560 < 4294967296)
    (hFit : base.toNat + 560 ≤ initial.mem.pages * 65536) :
    heap.top.toNat + 48 + (8 : UInt64).toNat < 4294967296 ∧
    (store.mem.pages < FixedArrayBump.requiredPages heap.top 8 →
      FixedArrayBump.requiredPages heap.top 8 ≤ store.memoryCap «module» 0) := by
  have ht := h.top
  refine ⟨by change _ + 48 + 8 < _; omega, ?_⟩
  intro hGrowth
  rw [h.pages] at hGrowth
  unfold FixedArrayBump.requiredPages at hGrowth
  change initial.mem.pages < (heap.top.toNat + 48 + 8 - 1) / 65536 + 1 at hGrowth
  omega

theorem Arena.pushed {initial store final : Store Unit} {base : UInt64} {count : Nat}
    {heap : Heap} {bytes : ByteArray} {byte : UInt8}
    (h : Arena initial base count heap store) (hCount : count < 5)
    (hFit32 : base.toNat + 560 < 4294967296)
    (hFit : base.toNat + 560 ≤ initial.mem.pages * 65536)
    (hOutput : heap.PackedOutput store final 8 (bytes.push byte))
    (hPages : final.mem.pages = (heap.allocatePackedStore store 8).mem.pages) :
    Arena initial base (count + 1) (heap.allocate 8) final ∧
    Buffer base (heap.allocate 8) final (allocatedNode heap.top 8 heap.nodes) (bytes.push byte) := by
  have ht := h.top
  have hFit' : takeFirstFitFrom 0 8 heap.nodes = none → heap.top.toNat + 48 + (8 : UInt64).toNat ≤ 4294967296 :=
    fun _ => by change _ + 48 + 8 ≤ _; omega
  have hSep := h.protection.allocated_disjoint 8 hFit'
  have hRoot := hOutput.owned.buffer.rootBound
  have hCapacity := allocated_capacity (8 : UInt64) heap.nodes
  have hAbove : base.toNat ≤ (allocatedNode heap.top 8 heap.nodes).root.toNat - 48 := by
    rcases hSep with hSep | hSep
    · exact hSep
    · change (allocatedRoot heap.top 8 heap.nodes).toNat + (allocatedCapacity 8 heap.nodes).toNat ≤ 0 at hSep
      change 8 ≤ (allocatedCapacity 8 heap.nodes).toNat at hCapacity
      omega
  refine ⟨⟨hOutput.heapAt, ?_, ?_, hOutput.frame.protects _ _ h.protection, ?_, ?_⟩,
    ⟨hOutput.owned.buffer.values, hOutput.owned.payload_protects, ?_, fun _ => hOutput.owned, fun _ => hAbove⟩⟩
  · have := heap.allocate_top_le 8
    change (heap.allocate 8).top.toNat ≤ heap.top.toNat + 48 + 8 at this
    omega
  · apply Nat.le_antisymm
    · rw [hPages]
      change (PackedAllocation.allocated store heap.top 8 heap.nodes).mem.pages ≤ _
      rw [PackedAllocation.pages_eq]
      apply allocated_pages_bound _ _ _ _ _ h.pages.le
      intro _
      change heap.top.toNat + 48 + 8 ≤ _
      omega
    · exact h.pages.ge.trans hOutput.frame.pages
  · intro address ha
    exact (hOutput.frame.bytes _ _ h.protection address (Nat.zero_le _) ha).trans (h.prefixBytes address ha)
  · exact (hOutput.memoryCap «module» 0).trans h.cap
  · simp

theorem Arena.released {initial store : Store Unit} {base : UInt64} {count : Nat}
    {heap : Heap} {node : FreeNode} {bytes : ByteArray}
    (h : Arena initial base count heap store)
    (hHeap : (heap.release node).At (heap.releaseStore store node))
    (hOwner : heap.OwnsPacked store node bytes)
    (hAbove : base.toNat ≤ node.root.toNat - 48) :
    Arena initial base count (heap.release node) (heap.releaseStore store node) := by
  refine ⟨hHeap, h.top, h.pages, ⟨h.protection.below, ?_⟩, ?_, h.cap⟩
  · intro other hOther
    rcases List.mem_cons.mp hOther with rfl | hOther
    · exact Or.inl hAbove
    · exact h.protection.separated other hOther
  · intro address ha
    exact (releasedStore_bytes store node.root (freeHead heap.nodes) heap.releases heap.frees
      hOwner.buffer.rootBound (by have := hOwner.buffer.addressBound; omega)
      address (Or.inl (by omega))).trans (h.prefixBytes address ha)

#print axioms need_small
#print axioms Arena.bump
#print axioms Arena.pushed
#print axioms Arena.released
end Project.LebU32.Recycling
