import Project.EulerRiemann.AllocationFrame
import Project.EulerRiemann.SweepResources
import Project.EulerRiemann.ReleaseMemory

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.Clob

structure OwnedGridAt (store : Store Unit) (node : FreeNode) (grid : Array Traversal.Cell) : Prop where
  rootBound : 48 ≤ node.root.toNat
  capacity : 8 * (7 * grid.size + 1) ≤ node.capacity.toNat
  addressBound : node.root.toNat + node.capacity.toNat < 4294967296
  memoryBound : node.root.toNat + node.capacity.toNat ≤ store.mem.pages * 65536
  fresh : FreshFixedArrayAt store node.root node.capacity 7
  values : Memory.GridAt store node.root grid

theorem OwnedGridAt.mem_congr {initial final : Store Unit} {node : FreeNode}
    {grid : Array Traversal.Cell} (hOwner : OwnedGridAt initial node grid)
    (hMem : final.mem = initial.mem) : OwnedGridAt final node grid := by
  refine ⟨hOwner.rootBound, hOwner.capacity, hOwner.addressBound, ?_, ?_, ?_⟩
  · rw [hMem]
    exact hOwner.memoryBound
  · simpa only [FreshFixedArrayAt, hMem] using hOwner.fresh
  · simpa only [Memory.GridAt, hMem] using hOwner.values

theorem OwnedGridAt.allocated {store : Store Unit} {source : FreeNode} {grid : Array Traversal.Cell}
    (hOwner : OwnedGridAt store source grid) (base need : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hSep : ∀ node ∈ nodes, regionsDisjoint source.region node.region)
    (hHeap : source.root.toNat + source.capacity.toNat ≤ base.toNat)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    OwnedGridAt (allocatedStore store base need nodes) source grid := by
  have hPages := allocated_pages_ge store base need nodes
  refine ⟨hOwner.rootBound, hOwner.capacity, hOwner.addressBound,
    hOwner.memoryBound.trans (Nat.mul_le_mul_right 65536 hPages),
    freshAt_allocated store base need 7 source nodes hOwner.rootBound
      (by have := hOwner.addressBound; omega) hOwner.fresh hList hSep hHeap hBump, ?_⟩
  apply hOwner.values.frame hPages
  intro address hLow hHigh
  exact allocated_bytes_in_region store base need source nodes hOwner.rootBound hList hSep hHeap hBump
    address (by omega) (by have := hOwner.capacity; omega)

theorem OwnedGridAt.writes {initial final : Store Unit} {source : FreeNode}
    {grid : Array Traversal.Cell} {target : UInt64} {size : Nat}
    (hOwner : OwnedGridAt initial source grid) (hWrites : Memory.WritesGrid initial final target size)
    (hSep : source.root.toNat + source.capacity.toNat ≤ target.toNat ∨
      target.toNat + 8 * (7 * size + 1) ≤ source.root.toNat - 48) :
    OwnedGridAt final source grid := by
  refine ⟨hOwner.rootBound, hOwner.capacity, hOwner.addressBound, ?_,
    hWrites.fresh_disjoint hOwner.rootBound (by have := hOwner.addressBound; omega)
      hOwner.fresh hSep, hWrites.grid hOwner.values ?_⟩
  · rw [hWrites.2.1]
    exact hOwner.memoryBound
  · have := hOwner.capacity
    omega

theorem OwnedGridAt.released {store : Store Unit} {source : FreeNode} {grid : Array Traversal.Cell}
    (hOwner : OwnedGridAt store source grid) (node : FreeNode) (head releases frees : UInt64)
    (hRoot : 48 ≤ node.root.toNat) (hRoot32 : node.root.toNat ≤ 4294967296)
    (hSep : regionsDisjoint source.region node.region) :
    OwnedGridAt (releasedStore store node.root head releases frees) source grid := by
  have hSourceRoot := hOwner.rootBound
  have hSourceCapacity := hOwner.capacity
  simp only [regionsDisjoint, FreeNode.region] at hSep
  refine ⟨hOwner.rootBound, hOwner.capacity, hOwner.addressBound, hOwner.memoryBound, ?_, ?_⟩
  · apply hOwner.fresh.frame_region (by have := hOwner.addressBound; omega) hOwner.rootBound
    intro address hLow hHigh
    exact releasedStore_bytes store node.root head releases frees hRoot hRoot32 address (by omega)
  · exact gridAt_releasedStore store node.root head releases frees source.root grid
      hRoot hRoot32 hOwner.values (by omega)

#print axioms OwnedGridAt.allocated
#print axioms OwnedGridAt.mem_congr
#print axioms OwnedGridAt.writes
#print axioms OwnedGridAt.released

end Project.EulerRiemann.Execution
