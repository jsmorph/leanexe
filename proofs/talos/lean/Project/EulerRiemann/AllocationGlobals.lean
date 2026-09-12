import Project.EulerRiemann.AllocationState

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ClobMatchFuel.BookAllocFit

def allocatedTop (base need : UInt64) (nodes : List FreeNode) : UInt64 :=
  match takeFirstFitFrom 0 need nodes with
  | some _ => base
  | none => base + 48 + need

theorem allocatedStore_top (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (hGlobal : store.globals.globals[0]? = some (.i64 base)) :
    (allocatedStore store base need nodes).globals.globals[0]? =
      some (.i64 (allocatedTop base need nodes)) := by
  obtain ⟨hLength, hRead⟩ := List.getElem_of_getElem? hGlobal
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simp only [allocatedStore, allocatedTop, hTake]
    unfold fixedArrayAllocFitStore
    split <;> simp [hGlobal]
  | none =>
    simp only [allocatedStore, allocatedTop, hTake]
    rw [bumpStore_globals]
    simp [hLength]

theorem allocatedStore_head (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hGlobal : store.globals.globals[1]? = some (.i64 (freeHead nodes))) :
    (allocatedStore store base need nodes).globals.globals[1]? =
      some (.i64 (freeHead (allocatedNodes need nodes))) := by
  obtain ⟨hLength, hRead⟩ := List.getElem_of_getElem? hGlobal
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simp only [allocatedStore, allocatedNodes, hTake,
      Project.ProofKit.FreeListMemory.remaining_head hList hTake, fixedArrayAllocFitStore]
    split <;> simp_all
  | none =>
    simp only [allocatedStore, allocatedNodes, hTake, bumpStore_globals]
    simpa using hGlobal

theorem allocatedStore_other_global (store : Store Unit) (base need : UInt64)
    (nodes : List FreeNode) (index : Nat) (h0 : index ≠ 0) (h1 : index ≠ 1) :
    (allocatedStore store base need nodes).globals.globals[index]? = store.globals.globals[index]? := by
  unfold allocatedStore
  split
  · unfold fixedArrayAllocFitStore
    split <;> simp [Ne.symm h1]
  · rw [bumpStore_globals]
    simp [Ne.symm h0]

theorem allocatedStore_memoryCap (store : Store Unit) (base need : UInt64)
    (nodes : List FreeNode) (m : Wasm.Module) (index : Nat) :
    (allocatedStore store base need nodes).memoryCap m index = store.memoryCap m index := by
  unfold allocatedStore
  split
  · rfl
  · unfold bumpStore Project.ProofKit.MemoryGrowth.ensured
    split <;> rfl

theorem allocatedTop_toNat (base need : UInt64) (nodes : List FreeNode)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    (allocatedTop base need nodes).toNat =
      if takeFirstFitFrom 0 need nodes = none then base.toNat + 48 + need.toNat else base.toNat := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice => simp [allocatedTop, hTake]
  | none =>
    have hFit := hBump hTake
    have h48 : (48 : UInt64).toNat = 48 := rfl
    simp only [allocatedTop, hTake, ite_true, UInt64.toNat_add, h48]
    change ((base.toNat + 48) % 18446744073709551616 + need.toNat) %
      18446744073709551616 = base.toNat + 48 + need.toNat
    omega

theorem allocated_below_top (base need : UInt64) (nodes : List FreeNode)
    (hBelow : ∀ node ∈ nodes, node.root.toNat + node.capacity.toNat ≤ base.toNat)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    (allocatedNode base need nodes).root.toNat + (allocatedNode base need nodes).capacity.toNat ≤
      (allocatedTop base need nodes).toNat ∧
    (∀ node ∈ allocatedNodes need nodes,
      node.root.toNat + node.capacity.toNat ≤ (allocatedTop base need nodes).toNat) := by
  have hTop := allocatedTop_toNat base need nodes hBump
  have hGrowth : base.toNat ≤ (allocatedTop base need nodes).toNat := by rw [hTop]; split <;> omega
  refine ⟨?_, fun node hNode => (hBelow node (allocatedNodes_mem need nodes node hNode)).trans hGrowth⟩
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simpa only [allocatedNode, allocatedRoot, allocatedCapacity, allocatedTop, hTake] using
      hBelow choice.node (takeFirstFitFrom_some_mem hTake)
  | none =>
    have hFit := hBump hTake
    have hRoot := Project.ProofKit.Allocation.root_toNat base (by omega)
    simp only [allocatedNode, allocatedRoot, allocatedCapacity, hTake, hRoot, hTop, ite_true]
    exact Nat.le_refl _

#print axioms allocatedStore_top
#print axioms allocatedStore_head
#print axioms allocatedStore_other_global
#print axioms allocatedStore_memoryCap
#print axioms allocatedTop_toNat
#print axioms allocated_below_top

end Project.EulerRiemann.Execution
