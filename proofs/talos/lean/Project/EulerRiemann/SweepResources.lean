import Project.EulerRiemann.AllocationState
import Project.EulerRiemann.MemoryOwnership

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.Clob Project.ProofKit.FixedArrayCapacity
  Project.ProofKit.FixedArrayResult

theorem sweep_resources (initial final : Store Unit) (base count : UInt64)
    (size : Nat) (nodes : List FreeNode) (hSize : size ≤ 640000)
    (hList : FreeListAt initial.mem nodes)
    (hBelow : ∀ node ∈ nodes, node.root.toNat + node.capacity.toNat ≤ base.toNat)
    (hBump : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat size) 7) nodes = none →
      base.toNat + 48 + (8 + size * 56) < 4294967296)
    (hWrites : Memory.WritesGrid
      (writeLength
        (countedStore (allocatedStore initial base (normalizedCapacity (UInt64.ofNat size) 7) nodes) count)
        (allocatedRoot base (normalizedCapacity (UInt64.ofNat size) 7) nodes) (UInt64.ofNat size))
      final (allocatedRoot base (normalizedCapacity (UInt64.ofNat size) 7) nodes) size) :
    let need := normalizedCapacity (UInt64.ofNat size) 7
    let node := allocatedNode base need nodes
    48 ≤ node.root.toNat ∧
    8 * (7 * size + 1) ≤ node.capacity.toNat ∧
    node.root.toNat + node.capacity.toNat < 4294967296 ∧
    node.root.toNat + node.capacity.toNat ≤ final.mem.pages * 65536 ∧
    FreshFixedArrayAt final node.root node.capacity 7 ∧
    FreeListAt final.mem (allocatedNodes need nodes) ∧
    gridFreeSeparated node.root size (allocatedNodes need nodes) ∧
    (∀ other ∈ allocatedNodes need nodes, regionsDisjoint node.region other.region) ∧
    Memory.WritesGrid (countedStore (allocatedStore initial base need nodes) count)
      final node.root size := by
  let need := normalizedCapacity (UInt64.ofNat size) 7
  let node := allocatedNode base need nodes
  let allocated := countedStore (allocatedStore initial base need nodes) count
  have hWord : (UInt64.ofNat size).toNat = size := by
    apply UInt64.toNat_ofNat_of_lt'
    change size < 18446744073709551616
    omega
  have hNeed : need.toNat = 8 + size * 56 := by
    simpa only [hWord] using sweep_capacity_toNat (UInt64.ofNat size) (by omega)
  have hFit : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 := by
    intro hNone
    have := hBump hNone
    omega
  have hBounds := allocated_bounds initial base need nodes hList hFit
  change 48 ≤ node.root.toNat ∧ node.root.toNat + node.capacity.toNat ≤ 4294967296 ∧
    node.root.toNat + node.capacity.toNat ≤ allocated.mem.pages * 65536 at hBounds
  have hCapacity : 8 * (7 * size + 1) ≤ node.capacity.toNat := by
    have := allocated_capacity need nodes
    change need.toNat ≤ node.capacity.toNat at this
    omega
  have hStrict : node.root.toNat + node.capacity.toNat < 4294967296 :=
    allocated_strict_bound initial base need nodes hList (fun hNone => by
      have := hBump hNone
      omega)
  have hFresh : FreshFixedArrayAt allocated node.root node.capacity 7 :=
    allocated_fresh initial base need nodes hList hFit
  have hAllocatedList : FreeListAt allocated.mem (allocatedNodes need nodes) :=
    freeListAt_allocated initial base need nodes hList hBelow hFit
  have hSeparation := allocated_node_separated initial base need nodes hList hBelow hFit
  have hGridSep : gridFreeSeparated node.root size (allocatedNodes need nodes) := by
    intro other hOther
    have hDisjoint := hSeparation other hOther
    have hOther48 := (hAllocatedList.mem_bounds hOther).1
    change regionsDisjoint node.region other.region at hDisjoint
    simp only [regionsDisjoint, FreeNode.region] at hDisjoint
    omega
  have hTotal : Memory.WritesGrid allocated final node.root size :=
    (Memory.writeLength_frame allocated node.root size (by omega)).trans hWrites
  refine ⟨hBounds.1, hCapacity, hStrict, ?_,
    hTotal.fresh hBounds.1 (by omega) hFresh,
    hTotal.freeList hAllocatedList hGridSep, hGridSep, hSeparation, hTotal⟩
  rw [hTotal.2.1]
  exact hBounds.2.2

#print axioms sweep_resources

end Project.EulerRiemann.Execution
