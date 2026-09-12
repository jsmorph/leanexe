import Project.EulerRiemann.AllocationCapacity

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.Clob Project.ClobMatchFuel.BookAllocFit
  Project.ProofKit.FixedArrayCapacity Project.ProofKit.MemoryGrowth

def allocatedCapacity (need : UInt64) (nodes : List FreeNode) : UInt64 :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => choice.node.capacity
  | none => need

theorem fitStore_pages (store : Store Unit) (choice : FreeChoice) :
    (fixedArrayAllocFitStore store choice 7).mem.pages = store.mem.pages := by
  change (unlinkFreeChoice store.mem choice).pages = store.mem.pages
  unfold unlinkFreeChoice
  split <;> rfl

theorem allocated_capacity (need : UInt64) (nodes : List FreeNode) :
    need.toNat ≤ (allocatedCapacity need nodes).toNat := by
  unfold allocatedCapacity
  split
  · exact UInt64.le_iff_toNat_le.mp (takeFirstFitFrom_some_capacity ‹_›)
  · rfl

theorem allocated_bounds (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    48 ≤ (allocatedRoot base need nodes).toNat ∧
    (allocatedRoot base need nodes).toNat + (allocatedCapacity need nodes).toNat ≤ 4294967296 ∧
    (allocatedRoot base need nodes).toNat + (allocatedCapacity need nodes).toNat ≤
      (allocatedStore store base need nodes).mem.pages * 65536 := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    obtain ⟨h48, h32, hFit⟩ := hList.mem_bounds (takeFirstFitFrom_some_mem hTake)
    simpa only [allocatedRoot, allocatedCapacity, allocatedStore, hTake, fitStore_pages] using
      And.intro h48 (And.intro (Nat.le_of_lt h32) hFit)
  | none =>
    have hFit32 := hBump hTake
    have hRoot := Project.ProofKit.Allocation.root_toNat base (by omega)
    have hFit := bumpPages_fit store base need
    simp only [allocatedRoot, allocatedCapacity, allocatedStore, hTake, hRoot]
    refine ⟨by omega, hFit32, ?_⟩
    simpa only [bumpStore_pages, ensured_pages] using hFit

theorem allocated_fresh (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    FreshFixedArrayAt (allocatedStore store base need nodes) (allocatedRoot base need nodes)
      (allocatedCapacity need nodes) 7 := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simpa only [allocatedStore, allocatedRoot, allocatedCapacity, hTake] using
      freshFixedArrayAt_fixedArrayAllocFitStore 7 hList hTake
  | none =>
    simpa only [allocatedStore, allocatedRoot, allocatedCapacity, hTake] using
      bumpStore_fresh store base need (hBump hTake)

theorem allocated_pages_ge (store : Store Unit) (base need : UInt64) (nodes : List FreeNode) :
    store.mem.pages ≤ (allocatedStore store base need nodes).mem.pages := by
  unfold allocatedStore
  split
  · rw [fitStore_pages]
  · rw [bumpStore_pages]
    exact Nat.le_max_left ..

theorem allocated_pages_le (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (hPages : store.mem.pages ≤ 65536)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    (allocatedStore store base need nodes).mem.pages ≤ 65536 := by
  unfold allocatedStore
  split
  · simpa only [fitStore_pages] using hPages
  · rw [bumpStore_pages]
    exact max_le hPages (bumpPages_le base need (hBump ‹_›))

theorem sweep_allocated_bounds (store : Store Unit) (base : UInt64) (count : Nat)
    (nodes : List FreeNode) (hCount : count ≤ 640000) (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat count) 7) nodes = none →
      base.toNat + 48 + (8 + count * 56) ≤ 4294967296) :
    let need := normalizedCapacity (UInt64.ofNat count) 7
    let root := allocatedRoot base need nodes
    48 ≤ root.toNat ∧ root.toNat + 8 * (7 * count + 1) ≤ 4294967296 ∧
      root.toNat + 8 * (7 * count + 1) ≤
        (allocatedStore store base need nodes).mem.pages * 65536 := by
  have hCount64 : count < UInt64.size := by
    change count < 18446744073709551616
    omega
  have hWord : (UInt64.ofNat count).toNat = count := UInt64.toNat_ofNat_of_lt' hCount64
  have hNeed := sweep_capacity_toNat (UInt64.ofNat count) (by omega)
  rw [hWord] at hNeed
  dsimp only
  have hBounds := allocated_bounds store base (normalizedCapacity (UInt64.ofNat count) 7)
    nodes hList (by simpa only [hNeed] using hBump)
  have hCapacity := allocated_capacity (normalizedCapacity (UInt64.ofNat count) 7) nodes
  rw [hNeed] at hCapacity
  exact ⟨hBounds.1, by omega, by omega⟩

#print axioms fitStore_pages
#print axioms allocated_capacity
#print axioms allocated_bounds
#print axioms allocated_fresh
#print axioms allocated_pages_ge
#print axioms allocated_pages_le
#print axioms sweep_allocated_bounds

end Project.EulerRiemann.Execution
