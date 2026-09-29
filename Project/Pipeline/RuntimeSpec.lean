import Project.Pipeline.Allocation
import Project.Runtime.Defs

/-!
Specifications of the runtime functions that compiled code calls.
-/

namespace Project.Pipeline

open Wasm Project.Runtime Project.ProofKit

/- CodeLib's `Mem.read64_write64_same` is proved with `bv_decide`, which adds an
axiom for compiled code.  The kernel-checked `Memory.read64_write64` replaces it
here. -/
attribute [-simp] Wasm.Mem.read64_write64_same
attribute [local simp] Memory.read64_write64

/-- The payload size `alloc` requests for `bytes`: rounded up to a multiple of 8,
and at least 8. -/
def allocSize (bytes : UInt64) : UInt64 :=
  if (bytes + 7) / 8 * 8 < 8 then 8 else (bytes + 7) / 8 * 8

/-- `alloc bytes` runs `FixedArrayAllocate.program` for `allocSize bytes` payload
bytes with element width one and returns the new block's payload pointer. -/
theorem alloc_spec {m : Module} {typeIdx : Nat} (hMemory32 : m.memIs64 = false)
    (hImports : m.imports = []) (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (bytes : UInt64)
    (hHeap : heap.At store) (hRoom : heap.Room store m (48 + (allocSize bytes).toNat)) :
    TerminatesWith env m 0 store [.i64 bytes] fun final out =>
      final = heap.allocateStore store (allocSize bytes) 1 ∧
      out = [.i64 (FixedArrayAllocate.root heap.top (allocSize bytes) heap.free)] := by
  refine TerminatesWith.of_wp_entry_for (f := allocFunction typeIdx)
    (by simpa [hImports] using hFunc) ?_ (by simp [hImports])
  simp [allocFunction, allocBody, Function.toLocals, Function.numParams, wp_simp]
  refine wp_iff_cons rfl ?_
  by_cases hSmall : (bytes + 7) / 8 * 8 < 8
  · have hSize : allocSize bytes = 8 := by simp [allocSize, hSmall]
    simp [hSmall, wp_simp]
    show wp m _ _ store (FixedArraySearch.frame [.i64 bytes] [] [] 8 0 0 0 0 0) env
    rw [← hSize]
    exact array_allocation_spec m hMemory32 env store heap [.i64 bytes] [] [] 1 rfl
      (allocSize bytes) 1 0 0 0 0 0 hHeap hRoom _ _ fun _ _ _ _ => by simp [FixedArraySearch.frame, wp_simp]
  · have hSize : allocSize bytes = (bytes + 7) / 8 * 8 := by simp [allocSize, hSmall]
    simp [hSmall, wp_simp]
    show wp m _ _ store (FixedArraySearch.frame [.i64 bytes] [] [] ((bytes + 7) / 8 * 8) 0 0 0 0 0)
      env
    rw [← hSize]
    exact array_allocation_spec m hMemory32 env store heap [.i64 bytes] [] [] 1 rfl
      (allocSize bytes) 1 0 0 0 0 0 hHeap hRoom _ _ fun _ _ _ _ => by simp [FixedArraySearch.frame, wp_simp]

/-- The heap after `release` frees the object at `ptr`, whose header records
payload capacity `capacity`. -/
def Heap.release (heap : Heap) (ptr capacity : UInt64) : Heap :=
  { heap with
    free := { root := ptr, capacity } :: heap.free
    releases := heap.releases + 1
    frees := heap.frees + 1 }

/-- The store after `release` frees the object at `ptr`: its count word is zero,
its child-mask word links to the old free-list head, and the globals hold
`heap.release`. -/
def Heap.releaseStore (heap : Heap) (store : Store Unit) (ptr : UInt64) : Store Unit :=
  { store with
    globals := { globals := (heap.release ptr (store.mem.read64 (ptr - 32).toUInt32)).globals }
    mem := ((store.mem.write64 (ptr - 40).toUInt32 0).write64 (ptr - 40).toUInt32 0).write64
      (ptr - 8).toUInt32 (freeHead heap.free) }

/-- The locals of `release` for the object at `ptr` in its pending-list loop:
count one, the pending head, and the object being freed. -/
def releaseLocals (ptr pending object : UInt64) : Locals :=
  { params := [.i64 ptr]
    locals := [.i64 1, .i64 pending, .i64 object, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0] }

theorem release_run {m : Module} {typeIdx : Nat} (hImports : m.imports = [])
    (hFunc : m.funcs[2]? = some (releaseFunction typeIdx)) (env : HostEnv Unit) (heap : Heap)
    (store : Store Unit) (ptr : UInt64) (words : Array UInt64) (hHeap : heap.At store)
    (hOwned : heap.Owned store ptr words) :
    TerminatesWith env m 2 store [.i64 ptr] fun final out =>
      out = [] ∧ final = heap.releaseStore store ptr := by
  refine TerminatesWith.of_wp_entry_for (f := releaseFunction typeIdx)
    (by simpa [hImports] using hFunc) ?_ (by simp [hImports])
  have hBase := hOwned.base
  have hBelow := hOwned.below
  have hTop := hHeap.top
  have hFit := hOwned.address
  have hPtr : ptr ≠ 0 := by rintro rfl; simp at hBase
  have hSub : ∀ k : UInt64, k.toNat ≤ 48 → (ptr - k).toNat = ptr.toNat - k.toNat := fun k hk =>
    UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)
  have hAt : ∀ k : UInt64, k.toNat ≤ 48 →
      (ptr - k).toUInt32 = UInt32.ofNat (ptr.toNat - k.toNat) := fun k hk => by
    rw [Memory.toUInt32_eq_ofNat, hSub k hk, Nat.mod_eq_of_lt (by omega)]
  have hs48 : (ptr - 48).toNat = ptr.toNat - 48 := hSub 48 (by decide)
  have hs40 : (ptr - 40).toNat = ptr.toNat - 40 := hSub 40 (by decide)
  have hs8 : (ptr - 8).toNat = ptr.toNat - 8 := hSub 8 (by decide)
  have hm48 : (ptr.toNat - 48) % 4294967296 = ptr.toNat - 48 := Nat.mod_eq_of_lt (by omega)
  have hm40 : (ptr.toNat - 40) % 4294967296 = ptr.toNat - 40 := Nat.mod_eq_of_lt (by omega)
  have hm8 : (ptr.toNat - 8) % 4294967296 = ptr.toNat - 8 := Nat.mod_eq_of_lt (by omega)
  have hA48 : (ptr - 48).toUInt32 = UInt32.ofNat (ptr.toNat - 48) := hAt 48 (by decide)
  have hA40 : (ptr - 40).toUInt32 = UInt32.ofNat (ptr.toNat - 40) := hAt 40 (by decide)
  have hA8 : (ptr - 8).toUInt32 = UInt32.ofNat (ptr.toNat - 8) := hAt 8 (by decide)
  have h40 : (ptr - 40).toUInt32.toNat = ptr.toNat - 40 :=
    headerAddress_toNat (by simp; omega) (by omega)
  have h8 : (ptr - 8).toUInt32.toNat = ptr.toNat - 8 :=
    headerAddress_toNat (by simp; omega) (by omega)
  have hMagic : store.mem.read64 (UInt32.ofNat (ptr.toNat - 48)) = magic := by
    rw [← hA48]; exact hOwned.magic
  have hCount : store.mem.read64 (UInt32.ofNat (ptr.toNat - 40)) = 1 := by
    rw [← hA40]; exact hOwned.count
  have hMask : (store.mem.write64 (UInt32.ofNat (ptr.toNat - 40)) 0).read64
      (UInt32.ofNat (ptr.toNat - 8)) = 0 := by
    rw [← hA40, ← hA8,
      Memory.read64_write64_disjoint _ _ _ _ (by omega)]
    exact hOwned.childMask
  have hGlobals := hHeap.globals
  have hb48 : ptr.toNat - 48 + 8 ≤ store.mem.pages * 65536 := by omega
  have hb40 : ptr.toNat - 40 + 8 ≤ store.mem.pages * 65536 := by omega
  have hb8 : ptr.toNat - 8 + 8 ≤ store.mem.pages * 65536 := by omega
  have hc40 : ¬ store.mem.pages * 65536 < ptr.toNat - 40 + 8 := by omega
  have hc8 : ¬ store.mem.pages * 65536 < ptr.toNat - 8 + 8 := by omega
  simp [releaseFunction, releaseBody, dropReference, checkMagic, headerLoad, headerStore,
    incrementGlobal, releaseCount, releasePending, releaseObject, Function.toLocals,
    Function.numParams, ValueType.zero, wp_simp, hPtr]
  refine wp_iff_cons rfl ?_
  simp [wp_simp, hs48, hm48, hb48, hMagic]
  refine wp_iff_cons rfl ?_
  simp [wp_simp, hs40, hm40, hb40, hCount]
  refine wp_iff_cons rfl ?_
  simp [wp_simp, hGlobals, Heap.globals]
  refine wp_iff_cons rfl ?_
  simp [wp_simp, hs40, hm40, hb40]
  change wp m _ _ _ (releaseLocals ptr ptr 0) env
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st s => (st = { store with
        globals := { globals := [.i64 heap.top, .i64 (freeHead heap.free), .i64 heap.allocs,
          .i64 heap.retains, .i64 (heap.releases + 1), .i64 heap.frees] }
        mem := store.mem.write64 (UInt32.ofNat (ptr.toNat - 40)) 0 } ∧
        s = releaseLocals ptr ptr 0) ∨
      (st = heap.releaseStore store ptr ∧ s = releaseLocals ptr 0 ptr))
    (fun _ s => match s.get releasePending with
      | some (.i64 pending) => pending.toNat
      | _ => 0) (Or.inl ⟨rfl, rfl⟩) ?_
  rintro st s (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · simp only [releaseLocals, wp_simp, releasePending]
    simp only [Locals.get, Locals.set?]
    simp [hs40, hm40, hc40, hPtr]
    simp only [dropChildren, headerLoad, releaseMask, releaseObject, List.cons_append,
      List.nil_append, wp_simp]
    simp only [Locals.get, Locals.set?]
    simp [hs8, hm8, hc8, hMask]
    refine wp_iff_cons rfl ?_
    simp only [freeObject, incrementGlobal, headerStore, releaseObject, List.cons_append,
      List.nil_append, wp_simp]
    simp only [Locals.get]
    simp [hs40, hm40, hs8, hm8]
    refine ⟨hb40, hb8, ?_, by omega⟩
    simp [Heap.releaseStore, Heap.release, Heap.globals, freeHead, hA40, hA8]
  · simp [releaseLocals, wp_simp]

/-- `release` changes only the count and child-mask words of the header. -/
theorem Heap.releaseStore_bytes (heap : Heap) (store : Store Unit) {ptr : UInt64}
    (hBase : 48 ≤ ptr.toNat) (hFit : ptr.toNat < 4294967296) {address : Nat}
    (h : address < ptr.toNat - 48 ∨ ptr.toNat ≤ address) :
    (heap.releaseStore store ptr).mem.bytes address = store.mem.bytes address := by
  have h40 := headerAddress_toNat (ptr := ptr) (k := 40) (by simp; omega) hFit
  have h8 := headerAddress_toNat (ptr := ptr) (k := 8) (by simp; omega) hFit
  simp only [UInt64.reduceToNat] at h40 h8
  simp only [Heap.releaseStore]
  rw [Memory.write64_bytes_outside _ _ _ (by omega), Memory.write64_bytes_outside _ _ _ (by omega),
    Memory.write64_bytes_outside _ _ _ (by omega)]

theorem Heap.releaseStore_pages (heap : Heap) (store : Store Unit) (ptr : UInt64) :
    (heap.releaseStore store ptr).mem.pages = store.mem.pages := by
  simp [Heap.releaseStore, Wasm.Mem.write64_pages]

/-- An array borrowed outside a freed object stays borrowed after the release. -/
theorem Heap.Borrowed.release {heap : Heap} {store : Store Unit} {p q : UInt64}
    {ws qs : Array UInt64} (h : heap.Borrowed store p ws) (hOwned : heap.Owned store q qs)
    (hDisjoint : regionsDisjoint (p.toNat, 8 * (ws.size + 1))
      (q.toNat - 48, 48 + capacityAt store q)) :
    (heap.release q (store.mem.read64 (q - 32).toUInt32)).Borrowed (heap.releaseStore store q) p
      ws := by
  have hBase := hOwned.base
  have hFit := hOwned.address
  unfold regionsDisjoint at hDisjoint
  refine ⟨arrayAt_frame h.values (by rw [Heap.releaseStore_pages]) fun address hLow hHigh =>
      Heap.releaseStore_bytes heap store (by omega) (by omega) (by omega), h.below, ?_⟩
  intro node hNode
  simp only [Heap.release, List.mem_cons] at hNode
  rcases hNode with rfl | hNode
  · simp only [FreeNode.region, regionsDisjoint]
    simp only [capacityAt] at hDisjoint
    omega
  · exact h.separate node hNode

/-- An object owned outside a freed object stays owned after the release, with its
capacity word unchanged. -/
theorem Heap.Owned.release {heap : Heap} {store : Store Unit} {p q : UInt64}
    {ws qs : Array UInt64} (h : heap.Owned store p ws) (hOwned : heap.Owned store q qs)
    (hDisjoint : regionsDisjoint (p.toNat - 48, 48 + capacityAt store p)
      (q.toNat - 48, 48 + capacityAt store q)) :
    (heap.release q (store.mem.read64 (q - 32).toUInt32)).Owned (heap.releaseStore store q) p ws ∧
      capacityAt (heap.releaseStore store q) p = capacityAt store p := by
  have hBase := hOwned.base
  have hFit := hOwned.address
  have hpBase := h.base
  have hpFit := h.address
  unfold regionsDisjoint at hDisjoint
  have hBytes : ∀ address, p.toNat - 48 ≤ address → address < p.toNat + capacityAt store p →
      (heap.releaseStore store q).mem.bytes address = store.mem.bytes address :=
    fun address hLow hHigh => Heap.releaseStore_bytes heap store (by omega) (by omega) (by omega)
  refine ⟨h.frame (by rw [Heap.releaseStore_pages]) hBytes h.below fun node hNode => ?_,
    capacityAt_frame (by omega) (by omega) fun a hl hh => hBytes a hl (by omega)⟩
  simp only [Heap.release, List.mem_cons] at hNode
  rcases hNode with rfl | hNode
  · simp only [FreeNode.region, regionsDisjoint, capacityAt] at hDisjoint ⊢
    omega
  · exact h.separate node hNode

/-- Freeing an owned array keeps the allocator invariant, with the object's
block at the head of the free list. -/
theorem Heap.At.release {heap : Heap} {store : Store Unit} {ptr : UInt64}
    {words : Array UInt64} (hHeap : heap.At store) (hOwned : heap.Owned store ptr words) :
    (heap.release ptr (store.mem.read64 (ptr - 32).toUInt32)).At (heap.releaseStore store ptr) := by
  have hBase := hOwned.base
  have hFit := hOwned.address
  have hBelow := hOwned.below
  have hSeparate := hOwned.separate
  simp only [capacityAt] at hFit hBelow hSeparate
  have h40 := headerAddress_toNat (ptr := ptr) (k := 40) (by simp; omega) (by omega)
  have h32 := headerAddress_toNat (ptr := ptr) (k := 32) (by simp; omega) (by omega)
  have h8 := headerAddress_toNat (ptr := ptr) (k := 8) (by simp; omega) (by omega)
  simp only [UInt64.reduceToNat] at h40 h32 h8
  have hTop := hHeap.top
  have hPagesMax := hHeap.pages
  refine ⟨rfl, ?_, hHeap.base, hTop, hPagesMax, ?_, ?_⟩
  · apply FreeListAt.cons
    · show 48 ≤ ptr.toNat
      omega
    · exact hFit
    · show ptr.toNat + (store.mem.read64 (ptr - 32).toUInt32).toNat ≤
        (heap.releaseStore store ptr).mem.pages * 65536
      simp only [Heap.releaseStore, Wasm.Mem.write64_pages]
      omega
    · simp only [Heap.releaseStore]
      rw [Memory.read64_write64_disjoint _ _ _ _ (by omega), Memory.read64_write64]
    · simp only [Heap.releaseStore]
      rw [Memory.read64_write64_disjoint _ _ _ _ (by omega),
        Memory.read64_write64_disjoint _ _ _ _ (by omega),
        Memory.read64_write64_disjoint _ _ _ _ (by omega)]
    · simp only [Heap.releaseStore]
      rw [Memory.read64_write64]
    · intro other hOther
      have := hSeparate other hOther
      simp only [regionsDisjoint, FreeNode.region] at this ⊢
      omega
    · refine FreeListMemory.frame_headers hHeap.freeList (by simp [Heap.releaseStore])
        fun node hNode address hLow hHigh => heap.releaseStore_bytes store (by omega) (by omega) ?_
      have hNodeSeparate := hSeparate node hNode
      have := hHeap.above node hNode
      simp only [regionsDisjoint, FreeNode.region] at hNodeSeparate
      omega
  · simp only [Heap.release, List.mem_cons, forall_eq_or_imp]
    exact ⟨hBase, hHeap.above⟩
  · simp only [Heap.release, List.mem_cons, forall_eq_or_imp]
    exact ⟨hBelow, hHeap.below⟩

end Project.Pipeline
