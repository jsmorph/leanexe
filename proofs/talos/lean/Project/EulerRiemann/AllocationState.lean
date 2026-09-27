import Project.EulerRiemann.AllocationPreserve

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ClobMatchFuel.BookAllocFit

def allocatedNodes (need : UInt64) (nodes : List FreeNode) : List FreeNode :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => choice.remaining
  | none => nodes

def allocatedNode (base need : UInt64) (nodes : List FreeNode) : FreeNode :=
  { root := allocatedRoot base need nodes, capacity := allocatedCapacity need nodes }

theorem allocatedNodes_mem (need : UInt64) (nodes : List FreeNode) (node : FreeNode)
    (hNode : node ∈ allocatedNodes need nodes) : node ∈ nodes := by
  unfold allocatedNodes at hNode
  split at hNode
  · exact takeFirstFitFrom_some_remaining_mem ‹_› hNode
  · exact hNode

theorem allocated_strict_bound (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat < 4294967296) :
    (allocatedNode base need nodes).root.toNat +
      (allocatedNode base need nodes).capacity.toNat < 4294967296 := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simpa only [allocatedNode, allocatedRoot, allocatedCapacity, hTake] using
      (hList.mem_bounds (takeFirstFitFrom_some_mem hTake)).2.1
  | none =>
    have hFit := hBump hTake
    have hRoot := Project.ProofKit.Allocation.root_toNat base (by omega)
    simpa only [allocatedNode, allocatedRoot, allocatedCapacity, hTake, hRoot] using hFit

theorem allocated_node_separated (store : Store Unit) (base need : UInt64)
    (nodes : List FreeNode) (hList : FreeListAt store.mem nodes)
    (hBelow : ∀ node ∈ nodes, node.root.toNat + node.capacity.toNat ≤ base.toNat)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    ∀ node ∈ allocatedNodes need nodes,
      regionsDisjoint (allocatedNode base need nodes).region node.region := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simpa only [allocatedNodes, allocatedNode, allocatedRoot, allocatedCapacity, hTake] using
      hList.takeFirstFitFrom_node_disjoint hTake
  | none =>
    have hFit := hBump hTake
    have hRoot := Project.ProofKit.Allocation.root_toNat base (by omega)
    simp only [allocatedNodes, allocatedNode, allocatedRoot, allocatedCapacity, hTake]
    intro node hNode
    have hEnd := hBelow node hNode
    have h48 := (hList.mem_bounds hNode).1
    simp only [regionsDisjoint, FreeNode.region, hRoot]
    omega

theorem freeListAt_allocated (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hBelow : ∀ node ∈ nodes, node.root.toNat + node.capacity.toNat ≤ base.toNat)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    FreeListAt (allocatedStore store base need nodes).mem (allocatedNodes need nodes) := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simpa only [allocatedStore, allocatedNodes, hTake, fixedArrayAllocFitStore] using
      freeListAt_fixedArrayAllocFitMem 7 hList hTake
  | none =>
    simp only [allocatedStore, allocatedNodes, hTake]
    apply Project.ProofKit.FreeListMemory.frame_headers hList
    · rw [bumpStore_pages]
      exact Nat.le_max_left ..
    · intro node hNode address hLow hHigh
      have hEnd := hBelow node hNode
      exact bumpStore_bytes_outside store base need (hBump hTake) address (by omega)

#print axioms allocatedNodes_mem
#print axioms allocated_strict_bound
#print axioms allocated_node_separated
#print axioms freeListAt_allocated

end Project.EulerRiemann.Execution
