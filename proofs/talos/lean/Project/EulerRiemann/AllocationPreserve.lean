import Project.EulerRiemann.AllocationBounds
import Project.ProofKit.FreeListMemory

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ClobMatchFuel.BookAllocFit Project.ProofKit.MemoryGrowth

def gridFreeSeparated (source : UInt64) (count : Nat) (nodes : List FreeNode) : Prop :=
  ∀ node ∈ nodes, source.toNat + 8 * (7 * count + 1) ≤ node.root.toNat - 48 ∨
    node.root.toNat + node.capacity.toNat ≤ source.toNat

theorem gridAt_allocated (store : Store Unit) (base need source : UInt64)
    (nodes : List FreeNode) (grid : Array Traversal.Cell) (hList : FreeListAt store.mem nodes)
    (hGrid : Memory.GridAt store source grid) (hSep : gridFreeSeparated source grid.size nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      source.toNat + 8 * (7 * grid.size + 1) ≤ base.toNat) :
    Memory.GridAt (allocatedStore store base need nodes) source grid := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simp only [allocatedStore, hTake]
    apply hGrid.frame
    · rw [fitStore_pages]
    · intro address hLow hHigh
      exact Project.ProofKit.FreeListMemory.fit_bytes 7 source.toNat
        (source.toNat + 8 * (7 * grid.size + 1)) address hList hTake hSep hLow hHigh
  | none =>
    obtain ⟨hFit32, hBefore⟩ := hBump hTake
    simp only [allocatedStore, hTake]
    exact gridAt_bump store base need source grid hGrid hFit32 (Or.inl hBefore)

theorem allocated_disjoint (store : Store Unit) (base need source : UInt64)
    (nodes : List FreeNode) (count : Nat) (hList : FreeListAt store.mem nodes)
    (hSep : gridFreeSeparated source count nodes)
    (hNeed : need.toNat = 8 * (7 * count + 1))
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      source.toNat + 8 * (7 * count + 1) ≤ base.toNat) :
    source.toNat + 8 * (7 * count + 1) ≤ (allocatedRoot base need nodes).toNat ∨
      (allocatedRoot base need nodes).toNat + 8 * (7 * count + 1) ≤ source.toNat := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    have hMember := takeFirstFitFrom_some_mem hTake
    obtain ⟨h48, _, _⟩ := hList.mem_bounds hMember
    have hCapacity := UInt64.le_iff_toNat_le.mp (takeFirstFitFrom_some_capacity hTake)
    have hDisjoint := hSep choice.node hMember
    simp only [allocatedRoot, hTake]
    omega
  | none =>
    obtain ⟨hFit32, hBefore⟩ := hBump hTake
    have hRoot := Project.ProofKit.Allocation.root_toNat base (by omega)
    simp only [allocatedRoot, hTake, hRoot]
    omega

theorem gridAt_counted (store : Store Unit) (source count : UInt64)
    (grid : Array Traversal.Cell) (hGrid : Memory.GridAt store source grid) :
    Memory.GridAt (countedStore store count) source grid := hGrid

theorem freeListAt_ensured (store : Store Unit) (required : Nat) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes) : FreeListAt (ensured store required).mem nodes := by
  apply Project.ProofKit.FreeListMemory.frame_grow hList
  · rw [ensured_pages]
    exact Nat.le_max_left ..
  · exact ensured_bytes store required

#print axioms gridAt_allocated
#print axioms allocated_disjoint
#print axioms gridAt_counted
#print axioms freeListAt_ensured

end Project.EulerRiemann.Execution
