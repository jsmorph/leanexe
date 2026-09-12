import Project.EulerRiemann.AllocationState
import Project.EulerRiemann.MemoryOwnership

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.Clob Project.ClobMatchFuel.BookAllocFit

theorem allocated_bytes_in_region (store : Store Unit) (base need : UInt64)
    (source : FreeNode) (nodes : List FreeNode) (hRoot : 48 ≤ source.root.toNat)
    (hList : FreeListAt store.mem nodes)
    (hSep : ∀ node ∈ nodes, regionsDisjoint source.region node.region)
    (hHeap : source.root.toNat + source.capacity.toNat ≤ base.toNat)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296)
    (address : Nat) (hLow : source.root.toNat - 48 ≤ address)
    (hHigh : address < source.root.toNat + source.capacity.toNat) :
    (allocatedStore store base need nodes).mem.bytes address = store.mem.bytes address := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simp only [allocatedStore, hTake]
    apply Project.ProofKit.FreeListMemory.fit_bytes 7 (source.root.toNat - 48)
      (source.root.toNat + source.capacity.toNat) address hList hTake ?_ hLow hHigh
    intro node hNode
    have hDisjoint := hSep node hNode
    have hNode48 := (hList.mem_bounds hNode).1
    simp only [regionsDisjoint, FreeNode.region] at hDisjoint
    omega
  | none =>
    simp only [allocatedStore, hTake]
    exact bumpStore_bytes_outside store base need (hBump hTake) address (Or.inl (by omega))

theorem freshAt_allocated (store : Store Unit) (base need stride : UInt64)
    (source : FreeNode) (nodes : List FreeNode) (hRoot : 48 ≤ source.root.toNat)
    (hRoot32 : source.root.toNat < 4294967296)
    (hFresh : FreshFixedArrayAt store source.root source.capacity stride)
    (hList : FreeListAt store.mem nodes)
    (hSep : ∀ node ∈ nodes, regionsDisjoint source.region node.region)
    (hHeap : source.root.toNat + source.capacity.toNat ≤ base.toNat)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    FreshFixedArrayAt (allocatedStore store base need nodes) source.root source.capacity stride := by
  exact hFresh.frame_region hRoot32 hRoot
    (allocated_bytes_in_region store base need source nodes hRoot hList hSep hHeap hBump)

theorem allocated_region_disjoint (base need : UInt64)
    (source : FreeNode) (nodes : List FreeNode) (hRoot : 48 ≤ source.root.toNat)
    (hSep : ∀ node ∈ nodes, regionsDisjoint source.region node.region)
    (hHeap : source.root.toNat + source.capacity.toNat ≤ base.toNat)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    regionsDisjoint source.region (allocatedNode base need nodes).region := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simpa only [allocatedNode, allocatedRoot, allocatedCapacity, hTake] using
      hSep choice.node (takeFirstFitFrom_some_mem hTake)
  | none =>
    have hFit := hBump hTake
    have hAllocatedRoot := Project.ProofKit.Allocation.root_toNat base (by omega)
    simp only [allocatedNode, allocatedRoot, allocatedCapacity, hTake, FreeNode.region,
      regionsDisjoint, hAllocatedRoot]
    omega

theorem freshAt_sweep (initial final : Store Unit) (base need count stride : UInt64)
    (source : FreeNode) (nodes : List FreeNode) (size : Nat)
    (hRoot : 48 ≤ source.root.toNat) (hRoot32 : source.root.toNat < 4294967296)
    (hFresh : FreshFixedArrayAt initial source.root source.capacity stride)
    (hList : FreeListAt initial.mem nodes)
    (hSep : ∀ node ∈ nodes, regionsDisjoint source.region node.region)
    (hHeap : source.root.toNat + source.capacity.toNat ≤ base.toNat)
    (hNeed : 8 * (7 * size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296)
    (hWrites : Memory.WritesGrid (countedStore (allocatedStore initial base need nodes) count)
      final (allocatedRoot base need nodes) size) :
    FreshFixedArrayAt final source.root source.capacity stride := by
  have hAllocatedFresh : FreshFixedArrayAt
      (countedStore (allocatedStore initial base need nodes) count) source.root source.capacity stride :=
    freshAt_allocated initial base need stride source nodes hRoot hRoot32 hFresh hList hSep hHeap hBump
  have hDisjoint := allocated_region_disjoint base need source nodes hRoot hSep hHeap hBump
  have hCapacity := allocated_capacity need nodes
  have hAllocatedRoot := (allocated_bounds initial base need nodes hList hBump).1
  apply hWrites.fresh_disjoint hRoot hRoot32 hAllocatedFresh
  simp only [allocatedNode, regionsDisjoint, FreeNode.region] at hDisjoint
  omega

#print axioms allocated_bytes_in_region
#print axioms freshAt_allocated
#print axioms allocated_region_disjoint
#print axioms freshAt_sweep

end Project.EulerRiemann.Execution
