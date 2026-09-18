import Project.ProofKit.PackedHeap
import Project.ProofKit.PackedRelease

namespace Project.ProofKit
open Wasm Project.Runtime

structure OwnedPackedAt (store : Store Unit) (node : FreeNode) (bytes : ByteArray) : Prop where
  rootBound : 48 ≤ node.root.toNat
  capacity : bytes.size ≤ node.capacity.toNat
  addressBound : node.root.toNat + node.capacity.toNat < 4294967296
  memoryBound : node.root.toNat + node.capacity.toNat ≤ store.mem.pages * 65536
  fresh : PackedHeader.FreshAt store.mem node.root node.capacity
  values : PackedMemory.ByteArrayAt store.mem node.root.toNat bytes

theorem OwnedPackedAt.frame_region {initial final : Store Unit} {node : FreeNode}
    {bytes : ByteArray} (h : OwnedPackedAt initial node bytes)
    (hPages : initial.mem.pages ≤ final.mem.pages)
    (hBytes : ∀ address : Nat,
      node.root.toNat - 48 ≤ address → address < node.root.toNat + node.capacity.toNat →
      final.mem.bytes address = initial.mem.bytes address) : OwnedPackedAt final node bytes := by
  refine ⟨h.rootBound, h.capacity, h.addressBound,
    h.memoryBound.trans (Nat.mul_le_mul_right 65536 hPages),
    h.fresh.frame_region h.rootBound (by have := h.addressBound; omega) ?_, ?_⟩
  · intro address hLow hHigh
    exact hBytes address hLow (by omega)
  · exact h.values.frame hPages (fun _ hLow hHigh =>
      hBytes _ (by omega) (by have := h.capacity; omega))

end Project.ProofKit

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit

structure Heap.OwnsPacked (heap : Heap) (store : Store Unit) (node : FreeNode)
    (bytes : ByteArray) : Prop where
  buffer : OwnedPackedAt store node bytes
  below : node.root.toNat + node.capacity.toNat ≤ heap.top.toNat
  separated : ∀ other ∈ heap.nodes, regionsDisjoint node.region other.region

theorem Heap.OwnsPacked.protects {heap : Heap} {store : Store Unit} {node : FreeNode}
    {bytes : ByteArray} (h : heap.OwnsPacked store node bytes) :
    heap.Protects (node.root.toNat - 48) (node.root.toNat + node.capacity.toNat) := by
  refine ⟨h.below, ?_⟩
  intro other hOther
  have hSep := h.separated other hOther
  have hRoot := h.buffer.rootBound
  simp only [regionsDisjoint, FreeNode.region] at hSep
  omega

theorem Heap.Frame.ownsPacked {before after : Heap} {initial final : Store Unit}
    (h : before.Frame initial after final) (hHeap : after.At final)
    {node : FreeNode} {bytes : ByteArray}
    (hOwner : before.OwnsPacked initial node bytes) : after.OwnsPacked final node bytes := by
  have hProtected := h.protects _ _ hOwner.protects
  refine ⟨hOwner.buffer.frame_region h.pages (h.bytes _ _ hOwner.protects), hProtected.below, ?_⟩
  intro other hOther
  have hSep := hProtected.separated other hOther
  have hRoot := hOwner.buffer.rootBound
  have hOtherRoot := (hHeap.freeList.mem_bounds hOther).1
  simp only [regionsDisjoint, FreeNode.region]
  omega

theorem Heap.Frame.packed {before after : Heap} {initial final : Store Unit}
    (h : before.Frame initial after final) {ptr : Nat} {bytes : ByteArray}
    (hProtected : before.Protects ptr (ptr + bytes.size))
    (hBytes : PackedMemory.ByteArrayAt initial.mem ptr bytes) :
    PackedMemory.ByteArrayAt final.mem ptr bytes :=
  hBytes.frame h.pages (h.bytes _ _ hProtected)

theorem Heap.ownsPacked_written (heap : Heap) (initial final : Store Unit)
    (need : UInt64) (bytes : ByteArray) (hHeap : heap.At initial) (hNeed : bytes.size ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hWrites : ProofKit.Memory.WritesRange (heap.allocatePackedStore initial need) final
      (allocatedRoot heap.top need heap.nodes).toNat
      ((allocatedRoot heap.top need heap.nodes).toNat + bytes.size))
    (hBytes : PackedMemory.ByteArrayAt final.mem (allocatedRoot heap.top need heap.nodes).toNat bytes) :
    (heap.allocate need).OwnsPacked final (allocatedNode heap.top need heap.nodes) bytes := by
  have hBump' := fun h => (hBump h).le
  obtain ⟨hRoot, hBound, hFit⟩ := allocated_bounds initial heap.top need heap.nodes hHeap.freeList hBump'
  have hStrict := allocated_strict_bound initial heap.top need heap.nodes hHeap.freeList hBump
  have hFresh := PackedAllocation.fresh initial heap.top need heap.nodes hHeap.freeList hBump'
  refine ⟨⟨hRoot, hNeed.trans (allocated_capacity need heap.nodes), hStrict, ?_, ?_, hBytes⟩,
    (allocated_below_top heap.top need heap.nodes hHeap.below hBump').1,
    allocated_node_separated initial heap.top need heap.nodes hHeap.freeList hHeap.below hBump'⟩
  · change (allocatedRoot heap.top need heap.nodes).toNat + (allocatedCapacity need heap.nodes).toNat ≤ _
    rw [hWrites.2.1]
    change _ ≤ (PackedAllocation.allocated initial heap.top need heap.nodes).mem.pages * 65536
    rw [PackedAllocation.pages_eq]
    exact hFit
  · apply hFresh.frame_region hRoot (by omega)
    intro address _ hHigh
    exact hWrites.2.2 address (Or.inl hHigh)

theorem Heap.OwnsPacked.allocated {heap : Heap} {store : Store Unit} {source : FreeNode}
    {bytes : ByteArray} (hOwner : heap.OwnsPacked store source bytes)
    (need : UInt64) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296) :
    (heap.allocate need).OwnsPacked (heap.allocatePackedStore store need) source bytes :=
  (heap.frame_allocatePacked store need hHeap hBump).ownsPacked
    (heap.allocatePacked_at store need hHeap hBump) hOwner

structure Heap.PackedOutput (heap : Heap) (initial final : Store Unit)
    (need : UInt64) (bytes : ByteArray) : Prop where
  heapAt : (heap.allocate need).At final
  owned : (heap.allocate need).OwnsPacked final (allocatedNode heap.top need heap.nodes) bytes
  frame : heap.Frame initial (heap.allocate need) final
  pages : final.mem.pages ≤ 65536
  memoryCap : ∀ (module_ : Wasm.Module) (index : Nat),
    final.memoryCap module_ index = initial.memoryCap module_ index

theorem Heap.packedOutput (heap : Heap) (initial final : Store Unit)
    (need : UInt64) (bytes : ByteArray) (hHeap : heap.At initial) (hNeed : bytes.size ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hPages : initial.mem.pages ≤ 65536)
    (hWrites : ProofKit.Memory.WritesRange (heap.allocatePackedStore initial need) final
      (allocatedRoot heap.top need heap.nodes).toNat
      ((allocatedRoot heap.top need heap.nodes).toNat + bytes.size))
    (hBytes : PackedMemory.ByteArrayAt final.mem (allocatedRoot heap.top need heap.nodes).toNat bytes) :
    heap.PackedOutput initial final need bytes := by
  refine ⟨heap.packedWritten_at initial final need bytes.size hHeap hNeed (fun h => (hBump h).le) hWrites,
    heap.ownsPacked_written initial final need bytes hHeap hNeed hBump hWrites hBytes,
    heap.frame_packedWritten initial final need bytes.size hHeap hNeed (fun h => (hBump h).le) hWrites,
    ?_, ?_⟩
  · rw [hWrites.2.1]
    exact heap.allocatePackedStore_pages_le initial need hPages (fun h => (hBump h).le)
  · intro module_ index
    rw [hWrites.1]
    exact heap.allocatePackedStore_memoryCap initial need module_ index

theorem Heap.OwnsPacked.writesRange {heap : Heap} {initial final : Store Unit} {source : FreeNode}
    {bytes : ByteArray} {start stop : Nat} (hOwner : heap.OwnsPacked initial source bytes)
    (hWrites : ProofKit.Memory.WritesRange initial final start stop)
    (hSep : source.root.toNat + source.capacity.toNat ≤ start ∨ stop ≤ source.root.toNat - 48) :
    heap.OwnsPacked final source bytes :=
  ⟨hOwner.buffer.frame_region hWrites.2.1.ge
    (fun _ hLow hHigh => hWrites.2.2 _ (by omega)), hOwner.below, hOwner.separated⟩

theorem Heap.OwnsPacked.released {heap : Heap} {store : Store Unit} {source : FreeNode}
    {bytes : ByteArray} (hOwner : heap.OwnsPacked store source bytes) (node : FreeNode)
    (hRoot : 48 ≤ node.root.toNat) (hRoot32 : node.root.toNat ≤ 4294967296)
    (hSep : regionsDisjoint source.region node.region) :
    (heap.release node).OwnsPacked (heap.releaseStore store node) source bytes := by
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

theorem Heap.releasePacked_exact (env : HostEnv Unit) (module_ : Wasm.Module) (id : Nat)
    (heap : Heap) (initial : Store Unit) (node : FreeNode) (bytes : ByteArray)
    {typeIdx : Option Nat}
    (hFunction : module_.funcs[id - module_.imports.length]? =
      some { releaseFuncDef id with typeIdx := typeIdx })
    (hImport : module_.imports[id]? = none)
    (hHeap : heap.At initial) (hOwner : heap.OwnsPacked initial node bytes) :
    TerminatesWith env module_ id initial [.i64 node.root]
      (fun final values => values = [] ∧ final = heap.releaseStore initial node ∧
        (heap.release node).At final) := by
  apply (PackedRelease.exact env module_ id initial node.root (freeHead heap.nodes)
    heap.releases heap.frees hFunction hImport hOwner.buffer.rootBound
    (by have := hOwner.buffer.addressBound; omega)
    (by have := hOwner.buffer.memoryBound; omega)
    hOwner.buffer.fresh.magic hOwner.buffer.fresh.references hOwner.buffer.fresh.kind
    (by rw [hHeap.globals]; rfl) (by rw [hHeap.globals]; rfl)
    (by rw [hHeap.globals]; rfl)).mono
  rintro final values ⟨hValues, rfl⟩
  exact ⟨hValues, rfl, heap.release_at initial node hHeap hOwner.buffer.rootBound
    hOwner.buffer.addressBound hOwner.buffer.memoryBound hOwner.buffer.fresh.capacityWord
    hOwner.below hOwner.separated⟩

#print axioms Heap.Frame.ownsPacked
#print axioms Heap.ownsPacked_written
#print axioms Heap.packedOutput
#print axioms Heap.OwnsPacked.allocated
#print axioms Heap.OwnsPacked.writesRange
#print axioms Heap.OwnsPacked.released
#print axioms Heap.releasePacked_exact

end Project.EulerRiemann.Execution
