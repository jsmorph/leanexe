import Project.ProofKit.PackedAllocation
import Project.ProofKit.PackedReuseMemory

namespace Project.ProofKit.PackedAllocation
open Wasm Project.Runtime Project.ProofKit.Memory

def remaining (need : UInt64) (nodes : List FreeNode) : List FreeNode :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => choice.remaining
  | none => nodes

theorem allocated_pages (store : Store Unit) (base need : UInt64) (nodes : List FreeNode) :
    store.mem.pages ≤ (allocated store base need nodes).mem.pages := by
  unfold allocated
  split
  · rw [PackedReuse.reused_pages]
  · change store.mem.pages ≤ (MemoryGrowth.ensured store (FixedArrayBump.requiredPages base need)).mem.pages
    rw [MemoryGrowth.ensured_pages]
    exact Nat.le_max_left ..

theorem bump_bytes_outside (store : Store Unit) (base need : UInt64)
    (hFit32 : base.toNat + 48 ≤ 4294967296) (address : Nat)
    (hOutside : address < base.toNat ∨ base.toNat + 48 ≤ address) :
    (PackedAllocate.allocated store base need).mem.bytes address = store.mem.bytes address := by
  change (PackedHeader.headerMem (MemoryGrowth.ensured store
    (FixedArrayBump.requiredPages base need)).mem base need).bytes address = _
  rw [PackedHeader.bytes_outside _ _ _ hFit32 address hOutside, MemoryGrowth.ensured_bytes]

theorem bytes_preserved (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (lower upper address : Nat) (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none → base.toNat + 48 ≤ 4294967296)
    (hBelow : upper ≤ base.toNat)
    (hSep : ∀ node ∈ nodes, upper ≤ node.root.toNat - 48 ∨
      node.root.toNat + node.capacity.toNat ≤ lower)
    (hLow : lower ≤ address) (hHigh : address < upper) :
    (allocated store base need nodes).mem.bytes address = store.mem.bytes address := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | none =>
    simp only [allocated, hTake]
    exact bump_bytes_outside store base need (hBump hTake) address (Or.inl (by omega))
  | some choice =>
    simp only [allocated, hTake]
    exact PackedReuse.bytes_outside store nodes need choice lower upper address hList hTake hSep hLow hHigh

theorem byteArrayAt (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (pointer : Nat) (bytes : ByteArray) (hBytes : PackedMemory.ByteArrayAt store.mem pointer bytes)
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none → base.toNat + 48 ≤ 4294967296)
    (hBelow : pointer + bytes.size ≤ base.toNat)
    (hSep : ∀ node ∈ nodes, pointer + bytes.size ≤ node.root.toNat - 48 ∨
      node.root.toNat + node.capacity.toNat ≤ pointer) :
    PackedMemory.ByteArrayAt (allocated store base need nodes).mem pointer bytes := by
  apply hBytes.frame (allocated_pages store base need nodes)
  intro address hLow hHigh
  exact bytes_preserved store base need nodes pointer (pointer + bytes.size) address
    hList hBump hBelow hSep hLow hHigh

theorem freeListAt (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none → base.toNat + 48 ≤ 4294967296)
    (hBelow : ∀ node ∈ nodes, node.root.toNat + node.capacity.toNat ≤ base.toNat) :
    FreeListAt (allocated store base need nodes).mem (remaining need nodes) := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | none =>
    simp only [allocated, remaining, hTake]
    have hPages : store.mem.pages ≤ (PackedAllocate.allocated store base need).mem.pages := by
      simpa only [allocated, hTake] using allocated_pages store base need nodes
    apply FreeListMemory.frame_headers hList hPages
    intro node hNode address _ hHigh
    exact bump_bytes_outside store base need (hBump hTake) address
      (Or.inl (by have := hBelow node hNode; omega))
  | some choice =>
    simp only [allocated, remaining, hTake]
    exact PackedReuse.freeListAt store nodes need choice hList hTake

#print axioms byteArrayAt
#print axioms freeListAt

theorem root_disjoint (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (lower upper : Nat) (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none → base.toNat + 48 ≤ 4294967296)
    (hBelow : upper ≤ base.toNat)
    (hSep : ∀ node ∈ nodes, upper ≤ node.root.toNat - 48 ∨
      node.root.toNat + node.capacity.toNat ≤ lower) :
    upper ≤ (root base need nodes).toNat ∨ (root base need nodes).toNat + need.toNat ≤ lower := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | none =>
    have hb := hBump hTake
    simp only [root, hTake, UInt64.toNat_add, UInt64.toNat_ofNat]
    left
    omega
  | some choice =>
    have hDisjoint := hSep choice.node (takeFirstFitFrom_some_mem hTake)
    have hCapacity := takeFirstFitFrom_some_capacity hTake
    have hBounds := hList.mem_bounds (takeFirstFitFrom_some_mem hTake)
    rw [UInt64.le_iff_toNat_le] at hCapacity
    simp only [root, hTake]
    omega

theorem remaining_headers_disjoint (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none → base.toNat + 48 ≤ 4294967296)
    (hBelow : ∀ node ∈ nodes, node.root.toNat + node.capacity.toNat ≤ base.toNat) :
    ∀ node ∈ remaining need nodes, node.root.toNat ≤ (root base need nodes).toNat ∨
      (root base need nodes).toNat + need.toNat ≤ node.root.toNat - 48 := by
  intro node hNode
  cases hTake : takeFirstFitFrom 0 need nodes with
  | none =>
    simp only [remaining, hTake] at hNode
    have hb := hBump hTake
    have hNodeBelow := hBelow node hNode
    simp only [root, hTake, UInt64.toNat_add, UInt64.toNat_ofNat]
    left
    omega
  | some choice =>
    simp only [remaining, hTake] at hNode
    have hDisjoint := hList.takeFirstFitFrom_node_disjoint hTake node hNode
    have hCapacity := takeFirstFitFrom_some_capacity hTake
    have hChoiceBounds := hList.mem_bounds (takeFirstFitFrom_some_mem hTake)
    have hNodeBounds := hList.mem_bounds (takeFirstFitFrom_some_remaining_mem hTake hNode)
    rw [UInt64.le_iff_toNat_le] at hCapacity
    simp only [root, hTake]
    unfold regionsDisjoint FreeNode.region at hDisjoint
    omega

theorem freeListAt_after_writes (initial final : Store Unit) (base need count : UInt64)
    (nodes : List FreeNode) (hList : FreeListAt initial.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none → base.toNat + 48 ≤ 4294967296)
    (hBelow : ∀ node ∈ nodes, node.root.toNat + node.capacity.toNat ≤ base.toNat)
    (hWrites : WritesRange (FixedArrayAllocateNone.counted (allocated initial base need nodes) count) final
      (root base need nodes).toNat ((root base need nodes).toNat + need.toNat)) :
    FreeListAt final.mem (remaining need nodes) := by
  have hFree := freeListAt initial base need nodes hList hBump hBelow
  have hPages : (allocated initial base need nodes).mem.pages ≤ final.mem.pages := by
    rw [hWrites.2.1]
    exact Nat.le_refl _
  apply FreeListMemory.frame_headers (mem' := final.mem) hFree hPages
  intro node hNode address hLow hHigh
  have hDisjoint := remaining_headers_disjoint initial base need nodes hList hBump hBelow node hNode
  exact hWrites.2.2 address (by omega)

theorem byteArrayAt_after_writes (initial final : Store Unit) (base need count : UInt64)
    (nodes : List FreeNode) (pointer : Nat) (bytes : ByteArray)
    (hBytes : PackedMemory.ByteArrayAt initial.mem pointer bytes) (hList : FreeListAt initial.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none → base.toNat + 48 ≤ 4294967296)
    (hBelow : pointer + bytes.size ≤ base.toNat)
    (hSep : ∀ node ∈ nodes, pointer + bytes.size ≤ node.root.toNat - 48 ∨
      node.root.toNat + node.capacity.toNat ≤ pointer)
    (hWrites : WritesRange (FixedArrayAllocateNone.counted (allocated initial base need nodes) count) final
      (root base need nodes).toNat ((root base need nodes).toNat + need.toNat)) :
    PackedMemory.ByteArrayAt final.mem pointer bytes := by
  have hPreserved := byteArrayAt initial base need nodes pointer bytes hBytes hList hBump hBelow hSep
  exact PackedMemory.ByteArrayAt.writesRange
    (initial := FixedArrayAllocateNone.counted (allocated initial base need nodes) count) hPreserved hWrites
    (root_disjoint initial base need nodes pointer (pointer + bytes.size) hList hBump hBelow hSep)

#print axioms freeListAt_after_writes
#print axioms byteArrayAt_after_writes

end Project.ProofKit.PackedAllocation
