import LeanExe.Pipeline.Runtime
import LeanExe.Pipeline.Implements
import LeanExe.ProofKit.FixedArrayAllocate

namespace LeanExe.Pipeline

open Wasm LeanExe.Runtime LeanExe.ProofKit

/-- `top` after allocating `need` payload bytes. -/
def allocatedTop (base need : UInt64) (nodes : List FreeNode) : UInt64 :=
  match takeFirstFitFrom 0 need nodes with
  | some _ => base
  | none => base + 48 + need

/-- The free list after allocating `need` payload bytes. -/
def allocatedNodes (need : UInt64) (nodes : List FreeNode) : List FreeNode :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => if splitsFit need choice then shrinkFirstFit need nodes else choice.remaining
  | none => nodes

/-- The payload capacity of the block that allocation returns. -/
def allocatedCapacity (need : UInt64) (nodes : List FreeNode) : UInt64 :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => if splitsFit need choice then need else choice.node.capacity
  | none => need

/-- The allocator state after `FixedArrayAllocate.program` allocates `need`
payload bytes. -/
def Heap.allocate (heap : Heap) (need : UInt64) : Heap :=
  { heap with
    top := allocatedTop heap.top need heap.free
    free := allocatedNodes need heap.free
    allocs := heap.allocs + 1 }

/-- The store after that allocation, for element width `stride`. -/
def Heap.allocateStore (heap : Heap) (store : Store Unit) (need stride : UInt64) : Store Unit :=
  FixedArrayAllocateNone.counted (FixedArrayAllocate.allocated store heap.top need stride heap.free)
    heap.allocs

/-- A block that allocation returned, with payload pointer `root` and room for
`capacity` bytes: a fresh array header with element width `stride`, inside memory
and the 32-bit address space, below `top`, and outside every free block. -/
structure Heap.Block (heap : Heap) (store : Store Unit) (root capacity stride : UInt64) :
    Prop where
  fresh : FreshFixedArrayAt store root capacity stride
  base : 4096 + 48 ≤ root.toNat
  address : root.toNat + capacity.toNat < 4294967296
  memory : root.toNat + capacity.toNat ≤ store.mem.pages * 65536
  below : root.toNat + capacity.toNat ≤ heap.top.toNat
  separate : ∀ node ∈ heap.free,
    regionsDisjoint node.region (root.toNat - 48, 48 + capacity.toNat)

/-- `store'` has the globals and page count of `store` and differs from it only
in the bytes `[start, start + size)`. -/
structure WritesWithin (store store' : Store Unit) (start size : Nat) : Prop where
  globals : store'.globals = store.globals
  pages : store'.mem.pages = store.mem.pages
  bytes : ∀ address, address < start ∨ start + size ≤ address →
    store'.mem.bytes address = store.mem.bytes address

/-- An allocation of `need` payload bytes fits in a memory of 65,535 pages: when no free
block is reused, the new `top` stays within `65535 * 65536`. -/
def Heap.Fits (heap : Heap) (need : UInt64) : Prop :=
  takeFirstFitFrom 0 need heap.free = none → heap.top.toNat + 48 + need.toNat ≤ 4294901760

theorem Heap.Fits.fit32 {heap : Heap} {need : UInt64} (h : heap.Fits need) :
    takeFirstFitFrom 0 need heap.free = none → heap.top.toNat + 48 + need.toNat ≤ 4294967296 :=
  fun hNone => by have := h hNone; omega

/-- Memory has room for an allocation of `need` bytes that no free block fits: the block ends
inside the 32-bit address space, and the cap covers the pages it needs. -/
def Heap.Room (heap : Heap) (store : Store Unit) (m : Wasm.Module) (need : UInt64) : Prop :=
  takeFirstFitFrom 0 need heap.free = none →
    heap.top.toNat + 48 + need.toNat ≤ 4294967296 ∧
      (store.mem.pages < FixedArrayBump.requiredPages heap.top need →
        FixedArrayBump.requiredPages heap.top need ≤ store.memoryCap m 0)

/-- `FixedArrayAllocate.program` for at most `2 ^ 32` bytes, in a memory whose cap is at
most 65,535 pages: the program allocates a block that fits, or traps at `unreachable`, which
the assertion accepts when `aborts`.  When not `aborts`, the room rules out the trap. -/
theorem array_allocation_spec_runs (aborts : Bool) (m : Wasm.Module)
    (hMemory32 : m.memIs64 = false) (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (need stride previous current capacity next result : UInt64) (hHeap : heap.At store)
    (hNeed : need.toNat ≤ 4294967296) (hCap : store.memoryCap m 0 ≤ 65535)
    (Q : Assertion Unit) (rest : Wasm.Program) (hTrap : TrapOK aborts Q)
    (hRoom : aborts = false → heap.Room store m need)
    (hNext : heap.Fits need → ∀ previous current capacity next : UInt64,
      wp m rest Q (heap.allocateStore store need stride)
        (FixedArraySearch.frame params saved tail need previous current capacity next
          (FixedArrayAllocate.root heap.top need heap.free)) env) :
    wp m (FixedArrayAllocate.program start stride ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  have hTop := hHeap.top
  have hPages := hHeap.pages
  exact FixedArrayAllocate.program_spec_runs aborts m env store params saved tail start hStart
    heap.top need stride previous current capacity next result heap.allocs heap.free
    (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals])
    hHeap.freeList (by omega) hNeed hHeap.pages hMemory32 hCap Q rest
    (fun h => by subst h; exact hTrap) hRoom hNext

/-- `FixedArrayAllocate.program` for at most `2 ^ 32` bytes, in a memory whose cap is at
most 65,535 pages: the program traps at `unreachable` or allocates a block that fits. -/
theorem array_allocation_spec_or_abort (m : Wasm.Module) (hMemory32 : m.memIs64 = false)
    (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (need stride previous current capacity next result : UInt64) (hHeap : heap.At store)
    (hNeed : need.toNat ≤ 4294967296) (hCap : store.memoryCap m 0 ≤ 65535)
    (Q : Assertion Unit) (rest : Wasm.Program) (hTrap : ∀ st, Q (.Trap st "unreachable"))
    (hNext : heap.Fits need → ∀ previous current capacity next : UInt64,
      wp m rest Q (heap.allocateStore store need stride)
        (FixedArraySearch.frame params saved tail need previous current capacity next
          (FixedArrayAllocate.root heap.top need heap.free)) env) :
    wp m (FixedArrayAllocate.program start stride ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  have hTop := hHeap.top
  have hPages := hHeap.pages
  exact FixedArrayAllocate.program_spec_or_abort m env store params saved tail start hStart
    heap.top need stride previous current capacity next result heap.allocs heap.free
    (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals])
    hHeap.freeList (by omega) hNeed hHeap.pages hMemory32 hCap Q rest hTrap hNext

theorem fitStore_pages (store : Store Unit) (choice : FreeChoice) (stride : UInt64) :
    (fixedArrayAllocFitStore store choice stride).mem.pages = store.mem.pages := by
  change (unlinkFreeChoice store.mem choice).pages = store.mem.pages
  unfold unlinkFreeChoice
  split <;> rfl

theorem reuseStore_pages (store : Store Unit) (choice : FreeChoice) (need stride : UInt64) :
    (fixedArrayReuseStore store choice need stride).mem.pages = store.mem.pages := by
  unfold fixedArrayReuseStore
  split
  · simp [fixedArraySplitMem, fixedArrayHeaderMem, Wasm.Mem.write64_pages]
  · exact fitStore_pages store choice stride

theorem bumpStore_pages (store : Store Unit) (base need stride : UInt64) :
    (FixedArrayBump.allocated store base need stride).mem.pages =
      max store.mem.pages (FixedArrayBump.requiredPages base need) := by
  simp only [FixedArrayBump.allocated, fixedArrayAllocBumpStore_pages,
    MemoryGrowth.ensured_pages]

theorem bump_bytes_outside (store : Store Unit) (base need stride : UInt64)
    (hFit : base.toNat + 48 + need.toNat ≤ 4294967296) (address : Nat)
    (hOutside : address < base.toNat ∨ base.toNat + 48 ≤ address) :
    (FixedArrayBump.allocated store base need stride).mem.bytes address =
      store.mem.bytes address := by
  change (fixedArrayHeaderMem (MemoryGrowth.ensured store
    (FixedArrayBump.requiredPages base need)).mem base need stride).bytes address = _
  rw [FixedArrayHeader.bytes_outside _ base need stride (by omega) address hOutside,
    MemoryGrowth.ensured_bytes]

theorem allocated_pages_ge (store : Store Unit) (base need stride : UInt64)
    (nodes : List FreeNode) :
    store.mem.pages ≤ (FixedArrayAllocate.allocated store base need stride nodes).mem.pages := by
  unfold FixedArrayAllocate.allocated
  split
  · rw [reuseStore_pages]
  · rw [bumpStore_pages]
    exact Nat.le_max_left ..

theorem allocated_pages_le (store : Store Unit) (base need stride : UInt64)
    (nodes : List FreeNode) (pageLimit : Nat) (hPages : store.mem.pages ≤ pageLimit)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ pageLimit * 65536) :
    (FixedArrayAllocate.allocated store base need stride nodes).mem.pages ≤ pageLimit := by
  unfold FixedArrayAllocate.allocated
  split
  · rwa [reuseStore_pages]
  · rw [bumpStore_pages]
    apply max_le hPages
    have hFit := hBump ‹_›
    unfold FixedArrayBump.requiredPages
    omega

theorem allocatedTop_toNat (base need : UInt64) (nodes : List FreeNode)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    (allocatedTop base need nodes).toNat =
      if takeFirstFitFrom 0 need nodes = none then base.toNat + 48 + need.toNat
      else base.toNat := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice => simp [allocatedTop, hTake]
  | none =>
    have hFit := hBump hTake
    have h48 : (48 : UInt64).toNat = 48 := rfl
    simp only [allocatedTop, hTake, ite_true, UInt64.toNat_add, h48]
    change ((base.toNat + 48) % 18446744073709551616 + need.toNat) %
      18446744073709551616 = base.toNat + 48 + need.toNat
    omega

/-- Every block on the free list after an allocation starts where a block before
it started and is no larger. -/
theorem allocatedNodes_sub {mem : Mem} {need : UInt64} {nodes : List FreeNode}
    (hList : FreeListAt mem nodes) (node : FreeNode) (hNode : node ∈ allocatedNodes need nodes) :
    ∃ old ∈ nodes, node.root = old.root ∧ node.capacity.toNat ≤ old.capacity.toNat := by
  unfold allocatedNodes at hNode
  split at hNode
  · rename_i choice hTake
    split at hNode
    · rename_i hSplit
      obtain ⟨hFits, hLow, -⟩ := split_facts hList hTake hSplit
      obtain ⟨skipped, tail, hNodes, hShrink⟩ := shrinkFirstFit_decompose hTake
      rw [hShrink] at hNode
      rcases List.mem_append.mp hNode with hSkipped | hRest
      · exact ⟨node, by rw [hNodes]; exact List.mem_append_left _ hSkipped, rfl, Nat.le_refl _⟩
      · rcases List.mem_cons.mp hRest with rfl | hTail
        · exact ⟨choice.node, takeFirstFitFrom_some_mem hTake, rfl, by simp only; omega⟩
        · exact ⟨node, by rw [hNodes]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hTail),
            rfl, Nat.le_refl _⟩
    · exact ⟨node, takeFirstFitFrom_some_remaining_mem hTake hNode, rfl, Nat.le_refl _⟩
  · exact ⟨node, hNode, rfl, Nat.le_refl _⟩

/-- A region apart from every free block stays apart from every free block after
an allocation. -/
theorem allocatedNodes_apart {mem : Mem} {need : UInt64} {nodes : List FreeNode}
    (hList : FreeListAt mem nodes) {region : Nat × Nat}
    (h : ∀ node ∈ nodes, regionsDisjoint region node.region) :
    ∀ node ∈ allocatedNodes need nodes, regionsDisjoint region node.region := by
  intro node hNode
  obtain ⟨old, hOld, hRoot, hCapacity⟩ := allocatedNodes_sub hList node hNode
  have hApart := h old hOld
  have h48 := (hList.mem_bounds hOld).1
  simp only [regionsDisjoint, FreeNode.region] at hApart ⊢
  rw [hRoot]
  omega

/-- A reused block's object lies inside the free block it came from and ends where
that block ends. -/
theorem allocated_within {mem : Mem} {base need : UInt64} {nodes : List FreeNode}
    {choice : FreeChoice} (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) :
    choice.node.root.toNat ≤ (FixedArrayAllocate.root base need nodes).toNat ∧
      (FixedArrayAllocate.root base need nodes).toNat + (allocatedCapacity need nodes).toNat =
        choice.node.root.toNat + choice.node.capacity.toNat := by
  simp only [FixedArrayAllocate.root, allocatedCapacity, reuseRoot, hTake]
  split
  · rename_i hSplit
    obtain ⟨hFits, _, _, hRoot, _, h32, _⟩ := split_facts hList hTake hSplit
    rw [← hRoot, UInt64.toNat_add]
    have := (split_facts hList hTake hSplit).2.2.1
    simp only [UInt64.reduceToNat]
    omega
  · exact ⟨Nat.le_refl _, rfl⟩

theorem allocated_capacity (need : UInt64) (nodes : List FreeNode) :
    need.toNat ≤ (allocatedCapacity need nodes).toNat := by
  unfold allocatedCapacity
  split
  · rename_i choice hTake
    split
    · exact Nat.le_refl _
    · exact UInt64.le_iff_toNat_le.mp (takeFirstFitFrom_some_capacity hTake)
  · exact Nat.le_refl _

theorem allocated_fresh (store : Store Unit) (base need stride : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    FreshFixedArrayAt (FixedArrayAllocate.allocated store base need stride nodes)
      (FixedArrayAllocate.root base need nodes) (allocatedCapacity need nodes) stride := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    by_cases hSplit : splitsFit need choice = true
    · simpa only [FixedArrayAllocate.allocated, FixedArrayAllocate.root, allocatedCapacity, hTake,
        fixedArrayReuseStore, reuseRoot, hSplit, ite_true]
        using freshFixedArrayAt_fixedArraySplitMem stride hList hTake hSplit
    · simpa only [FixedArrayAllocate.allocated, FixedArrayAllocate.root, allocatedCapacity, hTake,
        fixedArrayReuseStore, reuseRoot, hSplit, Bool.false_eq_true, ite_false]
        using freshFixedArrayAt_fixedArrayAllocFitStore stride hList hTake
  | none =>
    simp only [FixedArrayAllocate.allocated, FixedArrayAllocate.root, allocatedCapacity, hTake]
    exact FixedArrayHeader.fresh (MemoryGrowth.ensured store (FixedArrayBump.requiredPages base need))
      base need stride (by have := hBump hTake; omega)

theorem allocated_freeList (store : Store Unit) (base need stride : UInt64)
    (nodes : List FreeNode) (hList : FreeListAt store.mem nodes)
    (hBelow : ∀ node ∈ nodes, node.root.toNat + node.capacity.toNat ≤ base.toNat)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    FreeListAt (FixedArrayAllocate.allocated store base need stride nodes).mem
      (allocatedNodes need nodes) := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    by_cases hSplit : splitsFit need choice = true
    · simpa only [FixedArrayAllocate.allocated, allocatedNodes, hTake, fixedArrayReuseStore,
        hSplit, ite_true] using freeListAt_fixedArraySplitMem stride hList hTake hSplit
    · simpa only [FixedArrayAllocate.allocated, allocatedNodes, hTake, fixedArrayReuseStore,
        hSplit, Bool.false_eq_true, ite_false, fixedArrayAllocFitStore]
        using freeListAt_fixedArrayAllocFitMem stride hList hTake
  | none =>
    simp only [FixedArrayAllocate.allocated, allocatedNodes, hTake]
    apply FreeListMemory.frame_headers hList
    · rw [bumpStore_pages]
      exact Nat.le_max_left ..
    · intro node hNode address _ hHigh
      have hEnd := hBelow node hNode
      exact bump_bytes_outside store base need stride (hBump hTake) address (Or.inl (by omega))

/-- Allocation leaves unchanged every byte of a region below `base` that lies
outside every free block. -/
theorem allocated_bytes_outside (store : Store Unit) (base need stride : UInt64)
    (nodes : List FreeNode) (start size : Nat) (hList : FreeListAt store.mem nodes)
    (hSep : ∀ node ∈ nodes, regionsDisjoint (start, size) node.region)
    (hBelow : start + size ≤ base.toNat)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296)
    (address : Nat) (hLow : start ≤ address) (hHigh : address < start + size) :
    (FixedArrayAllocate.allocated store base need stride nodes).mem.bytes address =
      store.mem.bytes address := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simp only [FixedArrayAllocate.allocated, hTake, fixedArrayReuseStore]
    split
    · rename_i hSplit
      apply split_bytes stride hList hTake hSplit
      have hDisjoint := hSep choice.node (takeFirstFitFrom_some_mem hTake)
      have hNode48 := (hList.mem_bounds (takeFirstFitFrom_some_mem hTake)).1
      simp only [regionsDisjoint, FreeNode.region] at hDisjoint
      omega
    apply FreeListMemory.fit_bytes stride start (start + size) address hList hTake ?_ hLow hHigh
    intro node hNode
    have hDisjoint := hSep node hNode
    have hNode48 := (hList.mem_bounds hNode).1
    simp only [regionsDisjoint, FreeNode.region] at hDisjoint
    omega
  | none =>
    simp only [FixedArrayAllocate.allocated, hTake]
    exact bump_bytes_outside store base need stride (hBump hTake) address (Or.inl (by omega))

theorem Heap.allocateStore_globals {heap : Heap} {store : Store Unit} (h : heap.At store)
    (need stride : UInt64) :
    (heap.allocateStore store need stride).globals.globals = (heap.allocate need).globals := by
  cases hTake : takeFirstFitFrom 0 need heap.free with
  | some choice =>
    have hHead := FreeListMemory.remaining_head h.freeList hTake
    by_cases hSplit : splitsFit need choice = true
    · simp only [Heap.allocateStore, Heap.allocate, FixedArrayAllocateNone.counted,
        FixedArrayAllocate.allocated, allocatedTop, allocatedNodes, hTake, fixedArrayReuseStore,
        hSplit, ite_true]
      simp [Heap.globals, h.globals, freeHead_shrinkFirstFit]
    simp only [Heap.allocateStore, Heap.allocate, FixedArrayAllocateNone.counted,
      FixedArrayAllocate.allocated, allocatedTop, allocatedNodes, hTake, fixedArrayReuseStore,
      hSplit, Bool.false_eq_true, ite_false, fixedArrayAllocFitStore]
    split <;> simp_all [Heap.globals, h.globals]
  | none =>
    have hGlobals : (MemoryGrowth.ensured store
        (FixedArrayBump.requiredPages heap.top need)).globals = store.globals := by
      unfold MemoryGrowth.ensured
      split <;> rfl
    simp only [Heap.allocateStore, Heap.allocate, FixedArrayAllocateNone.counted,
      FixedArrayAllocate.allocated, allocatedTop, allocatedNodes, hTake, FixedArrayBump.allocated,
      fixedArrayAllocBumpStore, hGlobals, h.globals]
    rfl

theorem Heap.At.allocate_block {heap : Heap} {store : Store Unit} {need : UInt64}
    (stride : UInt64) (h : heap.At store) (hFits : heap.Fits need) :
    (heap.allocate need).Block (heap.allocateStore store need stride)
      (FixedArrayAllocate.root heap.top need heap.free) (allocatedCapacity need heap.free)
      stride := by
  have hFresh := allocated_fresh store heap.top need stride heap.free h.freeList hFits.fit32
  have h48 : (48 : UInt64).toNat = 48 := rfl
  cases hTake : takeFirstFitFrom 0 need heap.free with
  | some choice =>
    have hMem := takeFirstFitFrom_some_mem hTake
    obtain ⟨_, h32, hMemory⟩ := h.freeList.mem_bounds hMem
    have hPages : (heap.allocateStore store need stride).mem.pages = store.mem.pages := by
      simp only [Heap.allocateStore, FixedArrayAllocateNone.counted,
        FixedArrayAllocate.allocated, hTake, reuseStore_pages]
    have hTop : (heap.allocate need).top = heap.top := by
      simp only [Heap.allocate, allocatedTop, hTake]
    obtain ⟨hWithinLow, hWithinEnd⟩ := allocated_within (base := heap.top) h.freeList hTake
    have hAbove := h.above _ hMem
    have hBelowNode := h.below _ hMem
    refine ⟨hFresh, by omega, by omega, by rw [hPages]; omega, by rw [hTop]; omega, ?_⟩
    intro node hNode
    by_cases hSplit : splitsFit need choice = true
    · have hFree : (heap.allocate need).free = shrinkFirstFit need heap.free := by
        simp only [Heap.allocate, allocatedNodes, hTake, hSplit, ite_true]
      have hCapacity : allocatedCapacity need heap.free = need := by
        simp only [allocatedCapacity, hTake, hSplit, ite_true]
      obtain ⟨hFits, hLow, hBase, _, _, _, _⟩ := split_facts h.freeList hTake hSplit
      obtain ⟨skipped, tail, hNodes, hShrink⟩ := shrinkFirstFit_decompose hTake
      rw [hFree, hShrink] at hNode
      rw [hCapacity] at hWithinEnd ⊢
      have hList := h.freeList
      rw [hNodes] at hList
      have hPair := hList.pairwise
      rw [List.pairwise_append] at hPair
      obtain ⟨_, hTailPair, hCross⟩ := hPair
      rcases List.mem_append.mp hNode with hSkipped | hRest
      · have := hCross node hSkipped choice.node List.mem_cons_self
        simp only [regionsDisjoint, FreeNode.region] at this ⊢
        omega
      · rcases List.mem_cons.mp hRest with rfl | hTail
        · simp only [regionsDisjoint, FreeNode.region]
          omega
        · have := List.rel_of_pairwise_cons hTailPair hTail
          simp only [regionsDisjoint, FreeNode.region] at this ⊢
          omega
    · have hFree : (heap.allocate need).free = choice.remaining := by
        simp only [Heap.allocate, allocatedNodes, hTake, hSplit, Bool.false_eq_true, ite_false]
      rw [hFree] at hNode
      have := h.freeList.takeFirstFitFrom_node_disjoint hTake node hNode
      simp only [regionsDisjoint, FreeNode.region] at this ⊢
      omega
  | none =>
    have hFit := hFits hTake
    have hRoot : FixedArrayAllocate.root heap.top need heap.free = heap.top + 48 := by
      simp only [FixedArrayAllocate.root, hTake]
    have hCapacity : allocatedCapacity need heap.free = need := by
      simp only [allocatedCapacity, hTake]
    have hRootNat : (heap.top + 48).toNat = heap.top.toNat + 48 := by
      simp only [UInt64.toNat_add, h48, Nat.reducePow]
      omega
    have hPages : (heap.allocateStore store need stride).mem.pages =
        (MemoryGrowth.ensured store (FixedArrayBump.requiredPages heap.top need)).mem.pages := by
      simp only [Heap.allocateStore, FixedArrayAllocateNone.counted,
        FixedArrayAllocate.allocated, hTake, FixedArrayBump.allocated,
        fixedArrayAllocBumpStore_pages]
    have hTop := allocatedTop_toNat heap.top need heap.free hFits.fit32
    have hBase := h.base
    rw [hRoot, hCapacity] at hFresh ⊢
    refine ⟨hFresh, by omega, by omega, ?_, ?_, ?_⟩
    · rw [hPages, hRootNat]
      exact FixedArrayBump.requiredPages_fit store heap.top need
    · show (heap.top + 48).toNat + need.toNat ≤ (allocatedTop heap.top need heap.free).toNat
      rw [hTop, hRootNat]
      simp [hTake]
    · intro node hNode
      have hNode' : node ∈ heap.free := by
        simpa only [Heap.allocate, allocatedNodes, hTake] using hNode
      have hEnd := h.below node hNode'
      have hAbove := h.above node hNode'
      simp only [regionsDisjoint, FreeNode.region, hRootNat]
      omega

theorem Heap.At.allocate {heap : Heap} {store : Store Unit} {need : UInt64}
    (stride : UInt64) (h : heap.At store) (hFits : heap.Fits need) :
    (heap.allocate need).At (heap.allocateStore store need stride) := by
  have hTop := allocatedTop_toNat heap.top need heap.free hFits.fit32
  have hGrowth : heap.top.toNat ≤ (heap.allocate need).top.toNat := by
    show heap.top.toNat ≤ (allocatedTop heap.top need heap.free).toNat
    rw [hTop]
    split <;> omega
  have h48 : (48 : UInt64).toNat = 48 := rfl
  refine ⟨Heap.allocateStore_globals h need stride,
    allocated_freeList store heap.top need stride heap.free h.freeList h.below hFits.fit32,
    h.base.trans hGrowth, ?_,
    allocated_pages_le store heap.top need stride heap.free 65535 h.pages
      (fun hNone => by have := hFits hNone; show heap.top.toNat + 48 + need.toNat ≤ 65535 * 65536; omega),
    fun node hNode => ?_, fun node hNode => ?_⟩
  rotate_left
  · obtain ⟨old, hOld, hRoot, _⟩ := allocatedNodes_sub h.freeList node hNode
    rw [hRoot]
    exact h.above old hOld
  · obtain ⟨old, hOld, hRoot, hCapacity⟩ := allocatedNodes_sub h.freeList node hNode
    have := h.below old hOld
    rw [hRoot]
    omega
  show (allocatedTop heap.top need heap.free).toNat ≤ _
  rw [hTop]
  split
  · rename_i hNone
    have hMemory := (h.allocate_block stride hFits).memory
    simp only [FixedArrayAllocate.root, allocatedCapacity, hNone, UInt64.toNat_add, h48,
      Nat.reducePow] at hMemory
    have := h.top
    have := h.pages
    omega
  · exact h.top.trans (Nat.mul_le_mul_right _
      (allocated_pages_ge store heap.top need stride heap.free))

/-- An array whose words keep their bytes, and which lies inside the new memory, is laid out
there too. -/
theorem arrayAt_frameIn {initial final : Store Unit} {ptr : UInt64} {words : Array UInt64}
    (h : UInt64Array.At initial ptr words)
    (hMem : ptr.toNat + 8 * (words.size + 1) ≤ final.mem.pages * 65536)
    (hBytes : ∀ address, ptr.toNat ≤ address → address < ptr.toNat + 8 * (words.size + 1) →
      final.mem.bytes address = initial.mem.bytes address) : UInt64Array.At final ptr words := by
  refine ⟨h.1, hMem, ?_, fun i hi => ?_⟩
  · refine (Memory.read64_congr ptr.toUInt32 fun j hj => ?_).trans h.2.2.1
    rw [h.pointerAddress_toNat]
    exact hBytes _ (by omega) (by omega)
  · refine (Memory.read64_congr _ fun j hj => ?_).trans (h.2.2.2 i hi)
    rw [h.elementAddress_toNat i hi]
    exact hBytes _ (by omega) (by omega)

theorem arrayAt_frame {initial final : Store Unit} {ptr : UInt64} {words : Array UInt64}
    (h : UInt64Array.At initial ptr words) (hPages : initial.mem.pages ≤ final.mem.pages)
    (hBytes : ∀ address, ptr.toNat ≤ address → address < ptr.toNat + 8 * (words.size + 1) →
      final.mem.bytes address = initial.mem.bytes address) : UInt64Array.At final ptr words :=
  arrayAt_frameIn h (h.2.1.trans (Nat.mul_le_mul_right _ hPages)) hBytes

theorem Heap.Borrowed.allocate {heap : Heap} {store : Store Unit}
    {need ptr : UInt64} {words : Array UInt64} (stride : UInt64)
    (h : heap.Borrowed store ptr words) (hHeap : heap.At store) (hFits : heap.Fits need) :
    (heap.allocate need).Borrowed (heap.allocateStore store need stride) ptr words := by
  have hBump : takeFirstFitFrom 0 need heap.free = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun h => by have := hFits h; omega
  refine ⟨arrayAt_frame h.values (allocated_pages_ge store heap.top need stride heap.free)
    (allocated_bytes_outside store heap.top need stride heap.free ptr.toNat
      (8 * (words.size + 1)) hHeap.freeList h.separate h.below hBump), ?_,
    allocatedNodes_apart hHeap.freeList h.separate⟩
  show ptr.toNat + 8 * (words.size + 1) ≤ (allocatedTop heap.top need heap.free).toNat
  have := h.below
  rw [allocatedTop_toNat heap.top need heap.free hBump]
  split <;> omega

/-- The words that `ptr` borrows lie outside the allocated block. -/
theorem Heap.Borrowed.disjoint_allocated {heap : Heap} {store : Store Unit} {ptr : UInt64}
    {words : Array UInt64} (h : heap.Borrowed store ptr words) (hHeap : heap.At store)
    (need : UInt64) :
    regionsDisjoint (ptr.toNat, 8 * (words.size + 1))
      ((FixedArrayAllocate.root heap.top need heap.free).toNat - 48,
        48 + (allocatedCapacity need heap.free).toNat) := by
  cases hTake : takeFirstFitFrom 0 need heap.free with
  | some choice =>
    have := h.separate _ (takeFirstFitFrom_some_mem hTake)
    have hWithin := allocated_within (base := heap.top) hHeap.freeList hTake
    simp only [regionsDisjoint, FreeNode.region] at this ⊢
    omega
  | none =>
    have h48 : (48 : UInt64).toNat = 48 := rfl
    have := h.below
    have := hHeap.top
    have := hHeap.pages
    simp only [FixedArrayAllocate.root, allocatedCapacity, hTake, regionsDisjoint,
      UInt64.toNat_add, h48, Nat.reducePow]
    omega


theorem Heap.allocateStore_memoryCaps (heap : Heap) (store : Store Unit) (need stride : UInt64) :
    (heap.allocateStore store need stride).memoryCaps = store.memoryCaps := by
  unfold Heap.allocateStore FixedArrayAllocateNone.counted FixedArrayAllocate.allocated
  split
  · simp only [fixedArrayReuseStore]
    split
    · rfl
    · simp [fixedArrayAllocFitStore]
  · simp [FixedArrayBump.allocated, fixedArrayAllocBumpStore, MemoryGrowth.ensured]
    split <;> rfl

theorem Heap.At.writesWithin {heap : Heap} {store store' : Store Unit}
    {root capacity stride : UInt64} (h : heap.At store)
    (hBlock : heap.Block store root capacity stride)
    (hWrites : WritesWithin store store' root.toNat capacity.toNat) : heap.At store' := by
  refine ⟨by rw [hWrites.globals]; exact h.globals, ?_, h.base, by rw [hWrites.pages]; exact h.top,
    by rw [hWrites.pages]; exact h.pages, h.above, h.below⟩
  apply FreeListMemory.frame_headers h.freeList hWrites.pages.ge
  intro node hNode address hLow hHigh
  apply hWrites.bytes
  have hSeparate := hBlock.separate node hNode
  have := hBlock.base
  have := h.above node hNode
  simp only [regionsDisjoint, FreeNode.region] at hSeparate
  omega

theorem Heap.Block.writesWithin {heap : Heap} {store store' : Store Unit}
    {root capacity stride : UInt64} (h : heap.Block store root capacity stride)
    (hWrites : WritesWithin store store' root.toNat capacity.toNat) :
    heap.Block store' root capacity stride :=
  ⟨FreshFixedArrayAt.frame (base := root) (by have := h.address; omega)
      (by have := h.base; omega) (Nat.le_refl _)
      (fun address hAddress => hWrites.bytes address (Or.inl hAddress)) h.fresh,
    h.base, h.address, by rw [hWrites.pages]; exact h.memory, h.below, h.separate⟩

theorem Heap.Borrowed.writesWithin {heap : Heap} {store store' : Store Unit}
    {ptr root capacity : UInt64} {words : Array UInt64} (h : heap.Borrowed store ptr words)
    (hDisjoint : regionsDisjoint (ptr.toNat, 8 * (words.size + 1))
      (root.toNat - 48, 48 + capacity.toNat))
    (hWrites : WritesWithin store store' root.toNat capacity.toNat) :
    heap.Borrowed store' ptr words := by
  refine ⟨arrayAt_frame h.values hWrites.pages.ge (fun address hLow hHigh => hWrites.bytes address ?_),
    h.below, h.separate⟩
  simp only [regionsDisjoint] at hDisjoint
  omega

/-- A header word `k` bytes before a payload pointer inside the 32-bit address
space. -/
theorem headerAddress_toNat {ptr k : UInt64} (hk : k.toNat ≤ ptr.toNat)
    (hFit : ptr.toNat < 4294967296) : (ptr - k).toUInt32.toNat = ptr.toNat - k.toNat := by
  rw [Memory.toUInt32_toNat, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
  omega

/-- An owned object keeps its header, capacity, and words when the page count does
not shrink and the bytes of its region, header included, are unchanged.  The
object must lie below the new heap's `top` and outside its free blocks. -/
theorem Heap.Owned.frameIn {heap heap' : Heap} {store store' : Store Unit} {ptr : UInt64}
    {words : Array UInt64} (h : heap.Owned store ptr words)
    (hMem : ptr.toNat + 8 * (words.size + 1) ≤ store'.mem.pages * 65536)
    (hBytes : ∀ address, ptr.toNat - 48 ≤ address → address < ptr.toNat + capacityAt store ptr →
      store'.mem.bytes address = store.mem.bytes address)
    (hBelow : ptr.toNat + capacityAt store ptr ≤ heap'.top.toNat)
    (hSeparate : ∀ node ∈ heap'.free,
      regionsDisjoint node.region (ptr.toNat - 48, 48 + capacityAt store ptr)) :
    heap'.Owned store' ptr words := by
  have hBase := h.base
  have hAddress := h.address
  have hWords := h.capacity
  have hHeader : ∀ k : UInt64, k.toNat ≤ 48 → 8 ≤ k.toNat →
      store'.mem.read64 (ptr - k).toUInt32 = store.mem.read64 (ptr - k).toUInt32 :=
    fun k hk h8 => Memory.read64_congr _ fun i hi => by
      rw [headerAddress_toNat (by omega) (by omega)]
      exact hBytes _ (by omega) (by omega)
  have hCapacity : capacityAt store' ptr = capacityAt store ptr := by
    unfold capacityAt
    rw [hHeader 32 (by decide) (by decide)]
  refine ⟨arrayAt_frameIn h.values hMem fun address hLow hHigh => hBytes address (by omega)
      (by omega), hBase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hHeader 48 (by decide) (by decide)]; exact h.magic
  · rw [hHeader 40 (by decide) (by decide)]; exact h.count
  · rw [hCapacity]; exact hWords
  · rw [hHeader 24 (by decide) (by decide)]; exact h.kind
  · rw [hHeader 16 (by decide) (by decide)]; exact h.width
  · rw [hHeader 8 (by decide) (by decide)]; exact h.childMask
  · rw [hCapacity]; exact hAddress
  · rw [hCapacity]; exact hBelow
  · rw [hCapacity]; exact hSeparate

theorem Heap.Owned.frame {heap heap' : Heap} {store store' : Store Unit} {ptr : UInt64}
    {words : Array UInt64} (h : heap.Owned store ptr words)
    (hPages : store.mem.pages ≤ store'.mem.pages)
    (hBytes : ∀ address, ptr.toNat - 48 ≤ address → address < ptr.toNat + capacityAt store ptr →
      store'.mem.bytes address = store.mem.bytes address)
    (hBelow : ptr.toNat + capacityAt store ptr ≤ heap'.top.toNat)
    (hSeparate : ∀ node ∈ heap'.free,
      regionsDisjoint node.region (ptr.toNat - 48, 48 + capacityAt store ptr)) :
    heap'.Owned store' ptr words :=
  h.frameIn (h.values.2.1.trans (Nat.mul_le_mul_right _ hPages)) hBytes hBelow hSeparate

theorem Heap.Owned.allocate {heap : Heap} {store : Store Unit}
    {need ptr : UInt64} {words : Array UInt64} (stride : UInt64)
    (h : heap.Owned store ptr words) (hHeap : heap.At store) (hFits : heap.Fits need) :
    (heap.allocate need).Owned (heap.allocateStore store need stride) ptr words := by
  have hBump : takeFirstFitFrom 0 need heap.free = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun h => by have := hFits h; omega
  have hBase := h.base
  have hBelow := h.below
  refine h.frame (allocated_pages_ge store heap.top need stride heap.free)
    (fun address hLow hHigh => allocated_bytes_outside store heap.top need stride heap.free
      (ptr.toNat - 48) (48 + capacityAt store ptr) hHeap.freeList
      (fun node hNode => ?_) (by omega) hBump address hLow (by omega)) ?_
    fun node hNode => regionsDisjoint_symm (allocatedNodes_apart hHeap.freeList
      (fun n hn => regionsDisjoint_symm (h.separate n hn)) node hNode)
  · have := h.separate node hNode
    unfold regionsDisjoint at this ⊢
    omega
  · show ptr.toNat + capacityAt store ptr ≤ (allocatedTop heap.top need heap.free).toNat
    rw [allocatedTop_toNat heap.top need heap.free hBump]
    split <;> omega

/-- An owned object lies outside the block the next allocation returns. -/
theorem Heap.Owned.disjoint_allocated {heap : Heap} {store : Store Unit} {ptr : UInt64}
    {words : Array UInt64} (h : heap.Owned store ptr words) (hHeap : heap.At store)
    (need : UInt64) :
    regionsDisjoint (ptr.toNat - 48, 48 + capacityAt store ptr)
      ((FixedArrayAllocate.root heap.top need heap.free).toNat - 48,
        48 + (allocatedCapacity need heap.free).toNat) := by
  have hBase := h.base
  cases hTake : takeFirstFitFrom 0 need heap.free with
  | some choice =>
    have := h.separate _ (takeFirstFitFrom_some_mem hTake)
    have hWithin := allocated_within (base := heap.top) hHeap.freeList hTake
    simp only [FreeNode.region, regionsDisjoint] at this ⊢
    omega
  | none =>
    have h48 : (48 : UInt64).toNat = 48 := rfl
    have := h.below
    have := hHeap.top
    have := hHeap.pages
    simp only [FixedArrayAllocate.root, allocatedCapacity, hTake, regionsDisjoint,
      UInt64.toNat_add, h48, Nat.reducePow]
    omega

theorem Heap.Owned.writesWithin {heap : Heap} {store store' : Store Unit}
    {ptr root capacity : UInt64} {words : Array UInt64} (h : heap.Owned store ptr words)
    (hDisjoint : regionsDisjoint (ptr.toNat - 48, 48 + capacityAt store ptr)
      (root.toNat - 48, 48 + capacity.toNat))
    (hRoot : 48 ≤ root.toNat)
    (hWrites : WritesWithin store store' root.toNat capacity.toNat) :
    heap.Owned store' ptr words := by
  have hBase := h.base
  refine h.frame hWrites.pages.ge (fun address hLow hHigh => hWrites.bytes address ?_) h.below
    h.separate
  simp only [regionsDisjoint] at hDisjoint
  omega

/-- Writes inside the payload of an owned object keep the allocator invariant. -/
theorem Heap.At.writesOwned {heap : Heap} {store store' : Store Unit} {ptr : UInt64}
    {words : Array UInt64} (h : heap.At store) (hOwned : heap.Owned store ptr words)
    (hWrites : WritesWithin store store' ptr.toNat (capacityAt store ptr)) : heap.At store' := by
  refine ⟨by rw [hWrites.globals]; exact h.globals, ?_, h.base, by rw [hWrites.pages]; exact h.top,
    by rw [hWrites.pages]; exact h.pages, h.above, h.below⟩
  apply FreeListMemory.frame_headers h.freeList hWrites.pages.ge
  intro node hNode address hLow hHigh
  apply hWrites.bytes
  have hSeparate := hOwned.separate node hNode
  have := hOwned.base
  have := h.above node hNode
  simp only [regionsDisjoint, FreeNode.region] at hSeparate
  omega

/-- An owned object whose payload changes, inside its capacity, to hold `words'` is owned
with the new words and the same capacity. -/
theorem Heap.Owned.rewrite {heap : Heap} {store store' : Store Unit} {ptr : UInt64}
    {words words' : Array UInt64} (h : heap.Owned store ptr words)
    (hWrites : WritesWithin store store' ptr.toNat (capacityAt store ptr))
    (hValues : UInt64Array.At store' ptr words')
    (hFit : 8 * (words'.size + 1) ≤ capacityAt store ptr) :
    heap.Owned store' ptr words' ∧ capacityAt store' ptr = capacityAt store ptr := by
  have hBase := h.base
  have hAddress := h.address
  have hHeader : ∀ k : UInt64, k.toNat ≤ 48 → 8 ≤ k.toNat →
      store'.mem.read64 (ptr - k).toUInt32 = store.mem.read64 (ptr - k).toUInt32 :=
    fun k hk h8 => Memory.read64_congr _ fun i hi => by
      rw [headerAddress_toNat (by omega) (by omega)]
      exact hWrites.bytes _ (Or.inl (by omega))
  have hCapacity : capacityAt store' ptr = capacityAt store ptr := by
    unfold capacityAt
    rw [hHeader 32 (by decide) (by decide)]
  refine ⟨⟨hValues, hBase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hCapacity⟩
  · rw [hHeader 48 (by decide) (by decide)]; exact h.magic
  · rw [hHeader 40 (by decide) (by decide)]; exact h.count
  · rw [hCapacity]; exact hFit
  · rw [hHeader 24 (by decide) (by decide)]; exact h.kind
  · rw [hHeader 16 (by decide) (by decide)]; exact h.width
  · rw [hHeader 8 (by decide) (by decide)]; exact h.childMask
  · rw [hCapacity]; exact hAddress
  · rw [hCapacity]; exact h.below
  · rw [hCapacity]; exact h.separate

/-- The capacity word of an object is unchanged when the bytes of its header are. -/
theorem capacityAt_frame {store store' : Store Unit} {ptr : UInt64} (hBase : 48 ≤ ptr.toNat)
    (hFit : ptr.toNat < 4294967296)
    (hBytes : ∀ address, ptr.toNat - 48 ≤ address → address < ptr.toNat →
      store'.mem.bytes address = store.mem.bytes address) :
    capacityAt store' ptr = capacityAt store ptr := by
  have h32 : (32 : UInt64).toNat = 32 := rfl
  unfold capacityAt
  congr 1
  exact Memory.read64_congr (m1 := store'.mem) (m2 := store.mem) _ fun i hi => by
    rw [headerAddress_toNat (by rw [h32]; omega) hFit, h32]
    exact hBytes _ (by omega) (by omega)

/-- An owned object survives an allocation followed by writes inside the new
block, with its capacity word unchanged. -/
theorem Heap.Owned.allocate_within {heap : Heap} {initial store : Store Unit}
    {need p : UInt64} {ws : Array UInt64} (h : heap.Owned initial p ws) (hHeap : heap.At initial)
    (hFits : heap.Fits need)
    (hWithin : WritesWithin (heap.allocateStore initial need 1) store
      (FixedArrayAllocate.root heap.top need heap.free).toNat
      (allocatedCapacity need heap.free).toNat) :
    (heap.allocate need).Owned store p ws ∧ capacityAt store p = capacityAt initial p := by
  have hBase := h.base
  have hAddress := h.address
  have hBlockBase := (hHeap.allocate_block 1 hFits).base
  have hDisjoint := h.disjoint_allocated hHeap need
  have hAllocated := h.allocate 1 hHeap hFits
  have hBump : takeFirstFitFrom 0 need heap.free = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun h => by have := hFits h; omega
  have hAllocatedBytes : ∀ address, p.toNat - 48 ≤ address → address < p.toNat + capacityAt initial p →
      (heap.allocateStore initial need 1).mem.bytes address = initial.mem.bytes address :=
    fun address hLow hHigh => allocated_bytes_outside initial heap.top need 1 heap.free
      (p.toNat - 48) (48 + capacityAt initial p) hHeap.freeList (fun node hNode => by
        have := h.separate node hNode
        unfold regionsDisjoint at this ⊢
        omega) (by have := h.below; omega) hBump address hLow (by omega)
  have hStoreBytes : ∀ address, p.toNat - 48 ≤ address → address < p.toNat + capacityAt initial p →
      store.mem.bytes address = initial.mem.bytes address := fun address hLow hHigh => by
    rw [hWithin.bytes address (by unfold regionsDisjoint at hDisjoint; omega)]
    exact hAllocatedBytes address hLow hHigh
  have hCapacity : capacityAt store p = capacityAt initial p :=
    capacityAt_frame (by omega) (by omega) fun address hLow hHigh =>
      hStoreBytes address hLow (by omega)
  have hSameCapacity : capacityAt (heap.allocateStore initial need 1) p = capacityAt initial p :=
    capacityAt_frame (by omega) (by omega) fun address hLow hHigh =>
      hAllocatedBytes address hLow (by omega)
  exact ⟨hAllocated.writesWithin (by rw [hSameCapacity]; exact hDisjoint) (by omega) hWithin,
    hCapacity⟩

/-- A borrowed array survives an allocation followed by writes inside the new
block. -/
theorem Heap.Borrowed.allocate_within {heap : Heap} {initial store : Store Unit}
    {need p : UInt64} {ws : Array UInt64} (h : heap.Borrowed initial p ws) (hHeap : heap.At initial)
    (hFits : heap.Fits need)
    (hWithin : WritesWithin (heap.allocateStore initial need 1) store
      (FixedArrayAllocate.root heap.top need heap.free).toNat
      (allocatedCapacity need heap.free).toNat) :
    (heap.allocate need).Borrowed store p ws :=
  (h.allocate 1 hHeap hFits).writesWithin (h.disjoint_allocated hHeap need) hWithin

theorem Heap.Block.capacity_eq {heap : Heap} {store : Store Unit} {root capacity stride : UInt64}
    (h : heap.Block store root capacity stride) : capacityAt store root = capacity.toNat := by
  rw [capacityAt, h.fresh.2.2.1]

/-- A block with element width one that holds `words` is an owned array. -/
theorem Heap.Block.owned {heap : Heap} {store : Store Unit} {root capacity : UInt64}
    {words : Array UInt64} (h : heap.Block store root capacity 1)
    (hValues : UInt64Array.At store root words)
    (hCapacity : 8 * (words.size + 1) ≤ capacity.toNat) : heap.Owned store root words := by
  have hRead : capacityAt store root = capacity.toNat := by
    rw [capacityAt, h.fresh.2.2.1]
  obtain ⟨hMagic, hCount, _, hKind, hWidth, hChild⟩ := h.fresh
  refine ⟨hValues, h.base, hMagic, hCount, ?_, hKind, hWidth, hChild, ?_, ?_, ?_⟩ <;> rw [hRead]
  · exact hCapacity
  · exact h.address
  · exact h.below
  · exact h.separate

/-- A borrowed array occupies a region of the heap. -/
theorem Heap.Borrowed.region {heap : Heap} {store : Store Unit} {p : UInt64}
    {ws : Array UInt64} (h : heap.Borrowed store p ws) :
    heap.Region (p.toNat, 8 * (ws.size + 1)) :=
  ⟨h.below, fun node hNode => regionsDisjoint_symm (h.separate node hNode)⟩

/-- An owned array's block is a region of the heap. -/
theorem Heap.Owned.region {heap : Heap} {store : Store Unit} {p : UInt64} {ws : Array UInt64}
    (h : heap.Owned store p ws) : heap.Region (block store p) := by
  have := h.below
  have := h.base
  exact ⟨by simp only [block]; omega, h.separate⟩

/-- A borrowed array whose region keeps its bytes and is a region of a heap at the new store
stays borrowed. -/
theorem Heap.Borrowed.keepIn {heap heap' : Heap} {store store' : Store Unit} {q : UInt64}
    {ws : Array UInt64} (h : heap.Borrowed store q ws) (hAt : heap'.At store')
    (hBytes : ∀ a, q.toNat ≤ a → a < q.toNat + 8 * (ws.size + 1) →
      store'.mem.bytes a = store.mem.bytes a)
    (hRegion : heap'.Region (q.toNat, 8 * (ws.size + 1))) : heap'.Borrowed store' q ws :=
  ⟨arrayAt_frameIn h.values (hRegion.below.trans hAt.top) hBytes, hRegion.below,
    fun node hNode => regionsDisjoint_symm (hRegion.separate node hNode)⟩

/-- An owned array whose block keeps its bytes and is a region of a heap at the new store
stays owned, with the same capacity. -/
theorem Heap.Owned.keepIn {heap heap' : Heap} {store store' : Store Unit} {q : UInt64}
    {ws : Array UInt64} (h : heap.Owned store q ws) (hAt : heap'.At store')
    (hBytes : ∀ a, (block store q).1 ≤ a → a < (block store q).1 + (block store q).2 →
      store'.mem.bytes a = store.mem.bytes a)
    (hRegion : heap'.Region (block store q)) :
    heap'.Owned store' q ws ∧ capacityAt store' q = capacityAt store q := by
  have := h.base
  have := h.address
  have := h.capacity
  have := hAt.top
  have hBelow := hRegion.below
  simp only [block] at hBytes hBelow hRegion
  exact ⟨h.frameIn (by omega) (fun a hl hh => hBytes a hl (by omega)) (by omega)
      hRegion.separate,
    capacityAt_frame (by omega) (by omega) fun a hl hh => hBytes a hl (by omega)⟩

/-- A step that keeps the regions apart from `gone` keeps each borrowed array apart from
them. -/
theorem Heap.Keeps.borrowed {heap heap' : Heap} {initial store : Store Unit}
    {gone fresh : List (Nat × Nat)} (h : heap.Keeps initial gone heap' store fresh)
    (hAt : heap'.At store) {p : UInt64} {ws : Array UInt64} (hp : heap.Borrowed initial p ws)
    (hApart : ∀ b ∈ gone, regionsDisjoint (p.toNat, 8 * (ws.size + 1)) b) :
    heap'.Borrowed store p ws ∧ ∀ b ∈ fresh, regionsDisjoint (p.toNat, 8 * (ws.size + 1)) b := by
  obtain ⟨hBytes, hRegion, hFresh⟩ := h _ hp.region (by show 0 < 8 * (ws.size + 1); omega) hApart
  exact ⟨hp.keepIn hAt hBytes hRegion, hFresh⟩

/-- A step that keeps the regions apart from `gone` keeps each owned array apart from them,
with its capacity. -/
theorem Heap.Keeps.owned {heap heap' : Heap} {initial store : Store Unit}
    {gone fresh : List (Nat × Nat)} (h : heap.Keeps initial gone heap' store fresh)
    (hAt : heap'.At store) {p : UInt64} {ws : Array UInt64} (hp : heap.Owned initial p ws)
    (hApart : ∀ b ∈ gone, regionsDisjoint (block initial p) b) :
    (heap'.Owned store p ws ∧ capacityAt store p = capacityAt initial p) ∧
      ∀ b ∈ fresh, regionsDisjoint (block initial p) b := by
  obtain ⟨hBytes, hRegion, hFresh⟩ := h _ hp.region (by simp [block]) hApart
  exact ⟨hp.keepIn hAt hBytes hRegion, hFresh⟩

/-- An allocation leaves the bytes of a region, which stays a region and lies apart from the
new block. -/
theorem Heap.Region.allocate {heap : Heap} {store : Store Unit} {r : Nat × Nat}
    {need : UInt64} (stride : UInt64) (h : heap.Region r) (hHeap : heap.At store)
    (hFits : heap.Fits need) :
    (heap.allocate need).Region r ∧
      (∀ a, r.1 ≤ a → a < r.1 + r.2 →
        (heap.allocateStore store need stride).mem.bytes a = store.mem.bytes a) ∧
      regionsDisjoint r ((FixedArrayAllocate.root heap.top need heap.free).toNat - 48,
        48 + (allocatedCapacity need heap.free).toNat) := by
  have hBump : takeFirstFitFrom 0 need heap.free = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun h => by have := hFits h; omega
  have hBelow := h.below
  refine ⟨⟨?_, fun node hNode => regionsDisjoint_symm (allocatedNodes_apart hHeap.freeList
      (fun n hn => regionsDisjoint_symm (h.separate n hn)) node hNode)⟩,
    fun a hLow hHigh => allocated_bytes_outside store heap.top need stride heap.free r.1 r.2
      hHeap.freeList (fun node hNode => regionsDisjoint_symm (h.separate node hNode)) hBelow
      hBump a hLow hHigh, ?_⟩
  · show r.1 + r.2 ≤ (allocatedTop heap.top need heap.free).toNat
    rw [allocatedTop_toNat heap.top need heap.free hBump]
    split <;> omega
  cases hTake : takeFirstFitFrom 0 need heap.free with
  | some choice =>
    have := h.separate _ (takeFirstFitFrom_some_mem hTake)
    have hWithin := allocated_within (base := heap.top) hHeap.freeList hTake
    simp only [FreeNode.region, regionsDisjoint] at this ⊢
    omega
  | none =>
    have h48 : (48 : UInt64).toNat = 48 := rfl
    have := hHeap.top
    have := hHeap.pages
    simp only [FixedArrayAllocate.root, allocatedCapacity, hTake, regionsDisjoint,
      UInt64.toNat_add, h48, Nat.reducePow]
    omega

/-- What allocating a new array at `ptr` holding `words` leaves, with `heap'` the heap after
the allocation: the allocator invariant, the new owned array, every region of the heap before
kept and apart from the new object, and the memory limits. -/
structure Heap.NewArray (heap : Heap) (initial : Store Unit) (heap' : Heap) (store : Store Unit)
    (ptr : UInt64) (words : Array UInt64) : Prop where
  at_ : heap'.At store
  owned : heap'.Owned store ptr words
  keeps : heap.Keeps initial [] heap' store [block store ptr]
  caps : store.memoryCaps = initial.memoryCaps

/-- An allocation followed by writes that fill the new block with `words` leaves a
new array. -/
theorem Heap.newArray_of_writes {heap : Heap} {initial store : Store Unit}
    {need : UInt64} {words : Array UInt64} (hHeap : heap.At initial)
    (hFits : heap.Fits need)
    (hWithin : WritesWithin (heap.allocateStore initial need 1) store
      (FixedArrayAllocate.root heap.top need heap.free).toNat
      (allocatedCapacity need heap.free).toNat)
    (hValues : UInt64Array.At store (FixedArrayAllocate.root heap.top need heap.free) words)
    (hPayload : 8 * (words.size + 1) ≤ (allocatedCapacity need heap.free).toNat)
    (hCaps : store.memoryCaps = initial.memoryCaps) :
    heap.NewArray initial (heap.allocate need) store
      (FixedArrayAllocate.root heap.top need heap.free) words := by
  have hBlock := (hHeap.allocate_block 1 hFits).writesWithin hWithin
  have hCapacity := hBlock.capacity_eq
  refine ⟨(hHeap.allocate 1 hFits).writesWithin (hHeap.allocate_block 1 hFits) hWithin,
    hBlock.owned hValues hPayload, fun r hr _ _ => ?_, hCaps⟩
  obtain ⟨hRegion, hBytes, hApart⟩ := hr.allocate 1 hHeap hFits
  refine ⟨fun a hl hh => ?_, hRegion, fun b hb => ?_⟩
  · rw [hWithin.bytes a (by simp only [regionsDisjoint] at hApart; omega)]
    exact hBytes a hl hh
  · rw [List.mem_singleton.mp hb, block, hCapacity]
    exact hApart

/-- Every array borrowed before is still borrowed. -/
theorem Heap.NewArray.borrowed {heap heap' : Heap} {initial store : Store Unit} {ptr : UInt64}
    {words : Array UInt64} (h : heap.NewArray initial heap' store ptr words) :
    ∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store p ws :=
  fun _ _ hp => (h.keeps.borrowed h.at_ hp fun _ hb => nomatch hb).1

/-- Every array owned before is still owned, with its capacity. -/
theorem Heap.NewArray.ownedKeep {heap heap' : Heap} {initial store : Store Unit} {ptr : UInt64}
    {words : Array UInt64} (h : heap.NewArray initial heap' store ptr words) :
    ∀ p ws, heap.Owned initial p ws →
      heap'.Owned store p ws ∧ capacityAt store p = capacityAt initial p :=
  fun _ _ hp => (h.keeps.owned h.at_ hp fun _ hb => nomatch hb).1

/-- The new object lies apart from every array borrowed before. -/
theorem Heap.NewArray.borrowedApart {heap heap' : Heap} {initial store : Store Unit}
    {ptr : UInt64} {words : Array UInt64} (h : heap.NewArray initial heap' store ptr words) :
    ∀ p ws, heap.Borrowed initial p ws →
      regionsDisjoint (p.toNat, 8 * (ws.size + 1)) (ptr.toNat - 48, 48 + capacityAt store ptr) :=
  fun _ _ hp => (h.keeps.borrowed h.at_ hp fun _ hb => nomatch hb).2 _ (List.mem_singleton_self _)

/-- The new object lies apart from every array owned before. -/
theorem Heap.NewArray.ownedApart {heap heap' : Heap} {initial store : Store Unit}
    {ptr : UInt64} {words : Array UInt64} (h : heap.NewArray initial heap' store ptr words) :
    ∀ p ws, heap.Owned initial p ws →
      regionsDisjoint (p.toNat - 48, 48 + capacityAt initial p)
        (ptr.toNat - 48, 48 + capacityAt store ptr) :=
  fun _ _ hp => (h.keeps.owned h.at_ hp fun _ hb => nomatch hb).2 _ (List.mem_singleton_self _)

/-- Two new arrays in a row: every array owned before keeps its object and capacity,
and both new objects lie apart from every array borrowed or owned before. -/
theorem Heap.NewArray.two {heap heap1 heap2 : Heap} {initial store1 store2 : Store Unit}
    {ptr1 ptr2 : UInt64} {ws1 ws2 : Array UInt64}
    (h1 : heap.NewArray initial heap1 store1 ptr1 ws1)
    (h2 : heap1.NewArray store1 heap2 store2 ptr2 ws2) :
    (∀ p ws, heap.Owned initial p ws →
      heap2.Owned store2 p ws ∧ capacityAt store2 p = capacityAt initial p) ∧
    (∀ p ws, heap.Borrowed initial p ws →
      regionsDisjoint (p.toNat, 8 * (ws.size + 1)) (ptr1.toNat - 48, 48 + capacityAt store2 ptr1) ∧
      regionsDisjoint (p.toNat, 8 * (ws.size + 1)) (ptr2.toNat - 48, 48 + capacityAt store2 ptr2)) ∧
    (∀ p ws, heap.Owned initial p ws →
      regionsDisjoint (p.toNat - 48, 48 + capacityAt initial p)
        (ptr1.toNat - 48, 48 + capacityAt store2 ptr1) ∧
      regionsDisjoint (p.toNat - 48, 48 + capacityAt initial p)
        (ptr2.toNat - 48, 48 + capacityAt store2 ptr2)) := by
  have hCap1 : capacityAt store2 ptr1 = capacityAt store1 ptr1 := (h2.ownedKeep ptr1 ws1 h1.owned).2
  refine ⟨fun p ws h => ?_, fun p ws h => ?_, fun p ws h => ?_⟩
  · obtain ⟨hOwned1, hCapacity1⟩ := h1.ownedKeep p ws h
    obtain ⟨hOwned2, hCapacity2⟩ := h2.ownedKeep p ws hOwned1
    exact ⟨hOwned2, hCapacity2.trans hCapacity1⟩
  · rw [hCap1]
    exact ⟨h1.borrowedApart p ws h, h2.borrowedApart p ws (h1.borrowed p ws h)⟩
  · obtain ⟨hOwned1, hCapacity1⟩ := h1.ownedKeep p ws h
    have hApart2 := h2.ownedApart p ws hOwned1
    rw [hCapacity1] at hApart2
    rw [hCap1]
    exact ⟨h1.ownedApart p ws h, hApart2⟩

/-- The blocks of two arrays allocated one after the other are disjoint. -/
theorem Heap.NewArray.two_apart {heap heap1 heap2 : Heap} {initial store1 store2 : Store Unit}
    {ptr1 ptr2 : UInt64} {ws1 ws2 : Array UInt64}
    (h1 : heap.NewArray initial heap1 store1 ptr1 ws1)
    (h2 : heap1.NewArray store1 heap2 store2 ptr2 ws2) :
    regionsDisjoint (ptr1.toNat - 48, 48 + capacityAt store2 ptr1)
      (ptr2.toNat - 48, 48 + capacityAt store2 ptr2) := by
  rw [(h2.ownedKeep ptr1 ws1 h1.owned).2]
  exact h2.ownedApart ptr1 ws1 h1.owned

/-- An owned array can be lent: it is also borrowed, in the same heap. -/
theorem Heap.Owned.borrowed {heap : Heap} {store : Store Unit} {p : UInt64} {ws : Array UInt64}
    (h : heap.Owned store p ws) : heap.Borrowed store p ws := by
  have hCapacity := h.capacity
  have hBelow := h.below
  have hBase := h.base
  refine ⟨h.values, by omega, fun node hNode => ?_⟩
  have hSeparate := h.separate node hNode
  unfold regionsDisjoint at hSeparate ⊢
  omega

end LeanExe.Pipeline
