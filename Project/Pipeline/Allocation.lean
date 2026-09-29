import Project.Pipeline.Runtime
import Project.ProofKit.FixedArrayAllocate

namespace Project.Pipeline

open Wasm Project.Runtime Project.ProofKit

/-- `top` after allocating `need` payload bytes. -/
def allocatedTop (base need : UInt64) (nodes : List FreeNode) : UInt64 :=
  match takeFirstFitFrom 0 need nodes with
  | some _ => base
  | none => base + 48 + need

/-- The free list after allocating `need` payload bytes. -/
def allocatedNodes (need : UInt64) (nodes : List FreeNode) : List FreeNode :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => choice.remaining
  | none => nodes

/-- The payload capacity of the block that allocation returns. -/
def allocatedCapacity (need : UInt64) (nodes : List FreeNode) : UInt64 :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => choice.node.capacity
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

theorem Heap.Room.bump {heap : Heap} {store : Store Unit} {m : Module} {need : UInt64}
    (h : heap.Room store m (48 + need.toNat)) :
    heap.top.toNat + 48 + need.toNat ≤ 4294967296 ∧
      FixedArrayBump.requiredPages heap.top need ≤ store.memoryCap m 0 := by
  have hAddress := h.address
  have hCap := h.cap
  unfold FixedArrayBump.requiredPages
  omega

/-- `FixedArrayAllocate.program start stride` in any module with a 32-bit memory,
stated with the allocator state. -/
theorem array_allocation_spec (m : Wasm.Module) (hMemory32 : m.memIs64 = false)
    (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (need stride previous current capacity next result : UInt64) (hHeap : heap.At store)
    (hRoom : heap.Room store m (48 + need.toNat))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64,
      wp m rest Q (heap.allocateStore store need stride)
        (FixedArraySearch.frame params saved tail need previous current capacity next
          (FixedArrayAllocate.root heap.top need heap.free)) env) :
    wp m (FixedArrayAllocate.program start stride ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env :=
  FixedArrayAllocate.program_spec m env store params saved tail start hStart
    heap.top need stride previous current capacity next result heap.allocs heap.free
    (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals])
    hHeap.freeList (fun _ => hRoom.bump) hHeap.pages hMemory32 Q rest hNext

theorem fitStore_pages (store : Store Unit) (choice : FreeChoice) (stride : UInt64) :
    (fixedArrayAllocFitStore store choice stride).mem.pages = store.mem.pages := by
  change (unlinkFreeChoice store.mem choice).pages = store.mem.pages
  unfold unlinkFreeChoice
  split <;> rfl

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
  · rw [fitStore_pages]
  · rw [bumpStore_pages]
    exact Nat.le_max_left ..

theorem allocated_pages_le (store : Store Unit) (base need stride : UInt64)
    (nodes : List FreeNode) (pageLimit : Nat) (hPages : store.mem.pages ≤ pageLimit)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ pageLimit * 65536) :
    (FixedArrayAllocate.allocated store base need stride nodes).mem.pages ≤ pageLimit := by
  unfold FixedArrayAllocate.allocated
  split
  · rwa [fitStore_pages]
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

theorem allocatedNodes_mem (need : UInt64) (nodes : List FreeNode) (node : FreeNode)
    (hNode : node ∈ allocatedNodes need nodes) : node ∈ nodes := by
  unfold allocatedNodes at hNode
  split at hNode
  · exact takeFirstFitFrom_some_remaining_mem ‹_› hNode
  · exact hNode

theorem allocated_capacity (need : UInt64) (nodes : List FreeNode) :
    need.toNat ≤ (allocatedCapacity need nodes).toNat := by
  unfold allocatedCapacity
  split
  · exact UInt64.le_iff_toNat_le.mp (takeFirstFitFrom_some_capacity ‹_›)
  · exact Nat.le_refl _

theorem allocated_fresh (store : Store Unit) (base need stride : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296) :
    FreshFixedArrayAt (FixedArrayAllocate.allocated store base need stride nodes)
      (FixedArrayAllocate.root base need nodes) (allocatedCapacity need nodes) stride := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | some choice =>
    simpa only [FixedArrayAllocate.allocated, FixedArrayAllocate.root, allocatedCapacity, hTake]
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
    simpa only [FixedArrayAllocate.allocated, allocatedNodes, hTake, fixedArrayAllocFitStore]
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
    simp only [FixedArrayAllocate.allocated, hTake]
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
    simp only [Heap.allocateStore, Heap.allocate, FixedArrayAllocateNone.counted,
      FixedArrayAllocate.allocated, allocatedTop, allocatedNodes, hTake, fixedArrayAllocFitStore]
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

theorem Heap.At.allocate_block {heap : Heap} {store : Store Unit} {m : Module} {need : UInt64}
    (stride : UInt64) (h : heap.At store) (hRoom : heap.Room store m (48 + need.toNat)) :
    (heap.allocate need).Block (heap.allocateStore store need stride)
      (FixedArrayAllocate.root heap.top need heap.free) (allocatedCapacity need heap.free)
      stride := by
  have hFit := hRoom.bump.1
  have hAddress := hRoom.address
  have hFresh := allocated_fresh store heap.top need stride heap.free h.freeList (fun _ => hFit)
  have h48 : (48 : UInt64).toNat = 48 := rfl
  cases hTake : takeFirstFitFrom 0 need heap.free with
  | some choice =>
    have hMem := takeFirstFitFrom_some_mem hTake
    obtain ⟨_, h32, hMemory⟩ := h.freeList.mem_bounds hMem
    have hRoot : FixedArrayAllocate.root heap.top need heap.free = choice.node.root := by
      simp only [FixedArrayAllocate.root, hTake]
    have hCapacity : allocatedCapacity need heap.free = choice.node.capacity := by
      simp only [allocatedCapacity, hTake]
    have hPages : (heap.allocateStore store need stride).mem.pages = store.mem.pages := by
      simp only [Heap.allocateStore, FixedArrayAllocateNone.counted,
        FixedArrayAllocate.allocated, hTake, fitStore_pages]
    have hTop : (heap.allocate need).top = heap.top := by
      simp only [Heap.allocate, allocatedTop, hTake]
    have hFree : (heap.allocate need).free = choice.remaining := by
      simp only [Heap.allocate, allocatedNodes, hTake]
    rw [hRoot, hCapacity] at hFresh ⊢
    refine ⟨hFresh, h.above _ hMem, h32, by rw [hPages]; exact hMemory,
      by rw [hTop]; exact h.below _ hMem, ?_⟩
    rw [hFree]
    intro node hNode
    exact Or.symm (h.freeList.takeFirstFitFrom_node_disjoint hTake node hNode)
  | none =>
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
    have hTop := allocatedTop_toNat heap.top need heap.free (fun _ => hFit)
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

theorem Heap.At.allocate {heap : Heap} {store : Store Unit} {m : Module} {need : UInt64}
    (stride : UInt64) (h : heap.At store) (hRoom : heap.Room store m (48 + need.toNat)) :
    (heap.allocate need).At (heap.allocateStore store need stride) := by
  have hFit := hRoom.bump.1
  have hTop := allocatedTop_toNat heap.top need heap.free (fun _ => hFit)
  have hGrowth : heap.top.toNat ≤ (heap.allocate need).top.toNat := by
    show heap.top.toNat ≤ (allocatedTop heap.top need heap.free).toNat
    rw [hTop]
    split <;> omega
  have h48 : (48 : UInt64).toNat = 48 := rfl
  refine ⟨Heap.allocateStore_globals h need stride,
    allocated_freeList store heap.top need stride heap.free h.freeList h.below (fun _ => hFit),
    h.base.trans hGrowth, ?_,
    allocated_pages_le store heap.top need stride heap.free 65536 h.pages
      (fun _ => by show heap.top.toNat + 48 + need.toNat ≤ 65536 * 65536; omega),
    fun node hNode => h.above node (allocatedNodes_mem need heap.free node hNode),
    fun node hNode => (h.below node (allocatedNodes_mem need heap.free node hNode)).trans hGrowth⟩
  show (allocatedTop heap.top need heap.free).toNat ≤ _
  rw [hTop]
  split
  · rename_i hNone
    have hMemory := (h.allocate_block stride hRoom).memory
    simp only [FixedArrayAllocate.root, allocatedCapacity, hNone, UInt64.toNat_add, h48,
      Nat.reducePow] at hMemory
    have := h.top
    have := h.pages
    omega
  · exact h.top.trans (Nat.mul_le_mul_right _
      (allocated_pages_ge store heap.top need stride heap.free))

theorem arrayAt_frame {initial final : Store Unit} {ptr : UInt64} {words : Array UInt64}
    (h : UInt64Array.At initial ptr words) (hPages : initial.mem.pages ≤ final.mem.pages)
    (hBytes : ∀ address, ptr.toNat ≤ address → address < ptr.toNat + 8 * (words.size + 1) →
      final.mem.bytes address = initial.mem.bytes address) : UInt64Array.At final ptr words := by
  refine ⟨h.1, h.2.1.trans (Nat.mul_le_mul_right _ hPages), ?_, fun i hi => ?_⟩
  · refine (Memory.read64_congr ptr.toUInt32 fun j hj => ?_).trans h.2.2.1
    rw [h.pointerAddress_toNat]
    exact hBytes _ (by omega) (by omega)
  · refine (Memory.read64_congr _ fun j hj => ?_).trans (h.2.2.2 i hi)
    rw [h.elementAddress_toNat i hi]
    exact hBytes _ (by omega) (by omega)

theorem Heap.Borrowed.allocate {heap : Heap} {store : Store Unit} {m : Module}
    {need ptr : UInt64} {words : Array UInt64} (stride : UInt64)
    (h : heap.Borrowed store ptr words) (hHeap : heap.At store)
    (hRoom : heap.Room store m (48 + need.toNat)) :
    (heap.allocate need).Borrowed (heap.allocateStore store need stride) ptr words := by
  have hBump : takeFirstFitFrom 0 need heap.free = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun _ => hRoom.bump.1
  refine ⟨arrayAt_frame h.values (allocated_pages_ge store heap.top need stride heap.free)
    (allocated_bytes_outside store heap.top need stride heap.free ptr.toNat
      (8 * (words.size + 1)) hHeap.freeList h.separate h.below hBump), ?_,
    fun node hNode => h.separate node (allocatedNodes_mem need heap.free node hNode)⟩
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
    simpa only [FixedArrayAllocate.root, allocatedCapacity, hTake, FreeNode.region] using
      h.separate _ (takeFirstFitFrom_some_mem hTake)
  | none =>
    have h48 : (48 : UInt64).toNat = 48 := rfl
    have := h.below
    have := hHeap.top
    have := hHeap.pages
    simp only [FixedArrayAllocate.root, allocatedCapacity, hTake, regionsDisjoint,
      UInt64.toNat_add, h48, Nat.reducePow]
    omega

theorem Heap.allocate_top {heap : Heap} {store : Store Unit} {m : Module} {need : UInt64}
    (hRoom : heap.Room store m (48 + need.toNat)) :
    (heap.allocate need).top.toNat ≤ heap.top.toNat + (48 + need.toNat) := by
  show (allocatedTop heap.top need heap.free).toNat ≤ _
  rw [allocatedTop_toNat heap.top need heap.free (fun _ => hRoom.bump.1)]
  split <;> omega


theorem Heap.allocateStore_memoryCaps (heap : Heap) (store : Store Unit) (need stride : UInt64) :
    (heap.allocateStore store need stride).memoryCaps = store.memoryCaps := by
  unfold Heap.allocateStore FixedArrayAllocateNone.counted FixedArrayAllocate.allocated
  split <;> simp [fixedArrayAllocFitStore, FixedArrayBump.allocated, fixedArrayAllocBumpStore,
    MemoryGrowth.ensured] <;> split <;> rfl

/-- Room for an allocation followed by `rest` more bytes leaves room for `rest`
bytes after the allocation, in any store with the same memory limits. -/
theorem Heap.Room.after_allocate {heap : Heap} {store store' : Store Unit} {m : Module}
    {need : UInt64} {rest : Nat} (hRoom : heap.Room store m (48 + need.toNat + rest))
    (hCaps : store'.memoryCaps = store.memoryCaps) :
    (heap.allocate need).Room store' m rest := by
  have hAddress := hRoom.address
  have hCap := hRoom.cap
  have hTop := Heap.allocate_top (heap := heap) (store := store) (m := m) (need := need)
    ⟨by omega, by omega⟩
  refine ⟨by omega, ?_⟩
  have hSame : store'.memoryCap m 0 = store.memoryCap m 0 := by
    unfold Store.memoryCap; rw [hCaps]
  rw [hSame]
  omega

theorem Heap.allocate_pages (heap : Heap) (store : Store Unit) (need stride : UInt64) :
    (heap.allocateStore store need stride).mem.pages ≤
      max store.mem.pages ((heap.top.toNat + (48 + need.toNat) + 65535) / 65536) := by
  apply allocated_pages_le store heap.top need stride heap.free _ (Nat.le_max_left ..)
  intro _
  have hMax := Nat.mul_le_mul_right 65536
    (Nat.le_max_right store.mem.pages ((heap.top.toNat + (48 + need.toNat) + 65535) / 65536))
  omega

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

theorem header_address {ptr : UInt64} (k : UInt64) (hk : k.toNat ≤ 48)
    (hBase : 48 ≤ ptr.toNat) (hFit : ptr.toNat < 4294967296) :
    (ptr - k).toUInt32.toNat = ptr.toNat - k.toNat := by
  rw [Memory.toUInt32_toNat, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
  omega

/-- An owned object keeps its header, capacity, and words when the page count does
not shrink and the bytes of its region, header included, are unchanged.  The
object must lie below the new heap's `top` and outside its free blocks. -/
theorem Heap.Owned.frame {heap heap' : Heap} {store store' : Store Unit} {ptr : UInt64}
    {words : Array UInt64} (h : heap.Owned store ptr words)
    (hPages : store.mem.pages ≤ store'.mem.pages)
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
      rw [header_address k hk (by omega) (by omega)]
      exact hBytes _ (by omega) (by omega)
  have hCapacity : capacityAt store' ptr = capacityAt store ptr := by
    unfold capacityAt
    rw [hHeader 32 (by decide) (by decide)]
  refine ⟨arrayAt_frame h.values hPages fun address hLow hHigh => hBytes address (by omega)
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

theorem Heap.Owned.allocate {heap : Heap} {store : Store Unit} {m : Module}
    {need ptr : UInt64} {words : Array UInt64} (stride : UInt64)
    (h : heap.Owned store ptr words) (hHeap : heap.At store)
    (hRoom : heap.Room store m (48 + need.toNat)) :
    (heap.allocate need).Owned (heap.allocateStore store need stride) ptr words := by
  have hBump : takeFirstFitFrom 0 need heap.free = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun _ => hRoom.bump.1
  have hBase := h.base
  have hBelow := h.below
  refine h.frame (allocated_pages_ge store heap.top need stride heap.free)
    (fun address hLow hHigh => allocated_bytes_outside store heap.top need stride heap.free
      (ptr.toNat - 48) (48 + capacityAt store ptr) hHeap.freeList
      (fun node hNode => ?_) (by omega) hBump address hLow (by omega)) ?_
    fun node hNode => h.separate node (allocatedNodes_mem need heap.free node hNode)
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
    simp only [FixedArrayAllocate.root, allocatedCapacity, hTake, FreeNode.region,
      regionsDisjoint] at this ⊢
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

end Project.Pipeline
