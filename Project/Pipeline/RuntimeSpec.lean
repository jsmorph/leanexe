import Project.Pipeline.Allocation
import Project.Runtime.Defs
import Project.Runtime.Merge

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
payload capacity `capacity`: the block joins the free list in address order. -/
def Heap.release (heap : Heap) (ptr capacity : UInt64) : Heap :=
  { heap with
    free := insertFree ptr capacity heap.free
    releases := heap.releases + 1
    frees := heap.frees + 1 }

/-- The store after `release` frees the object at `ptr`: its count word is zero,
the header words of the freed block and of the free block below it are set as
`releaseMem` describes, and the globals hold `heap.release`. -/
def Heap.releaseStore (heap : Heap) (store : Store Unit) (ptr : UInt64) : Store Unit :=
  { store with
    globals := { globals := (heap.release ptr (store.mem.read64 (ptr - 32).toUInt32)).globals }
    mem := releaseMem (store.mem.write64 (ptr - 40).toUInt32 0) ptr
      (store.mem.read64 (ptr - 32).toUInt32) heap.free }

/-- The locals of `release` for the object at `ptr` in its pending-list loop:
count one, the pending head, the object being freed, and the free blocks before
and after its place in the free list. -/
def releaseLocals (ptr pending object previous current : UInt64) : Locals :=
  { params := [.i64 ptr]
    locals := [.i64 1, .i64 pending, .i64 object, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 previous, .i64 current] }

theorem Locals.get_with_values (s : Locals) (vs : List Value) (i : Nat) :
    ({ s with values := vs } : Locals).get i = s.get i := rfl

/-- `joinProgram ptrLocal nextLocal` sets the size and link words of `block`, at
local `ptrLocal`, for `joinNodes block rest`, where local `nextLocal` holds the
head of `rest`. -/
theorem joinProgram_spec {m : Module} (env : HostEnv Unit) (store : Store Unit) (s : Locals)
    (ptrLocal nextLocal : Nat) (block : FreeNode) (rest : List FreeNode)
    (hValues : s.values = []) (hPtr : s.get ptrLocal = some (.i64 block.root))
    (hNextLocal : s.get nextLocal = some (.i64 (freeHead rest)))
    (hRest : FreeListAt store.mem rest) (h48 : 48 ≤ block.root.toNat)
    (h32 : block.root.toNat + block.capacity.toNat < 4294967296)
    (hFit : block.root.toNat + block.capacity.toNat ≤ store.mem.pages * 65536)
    (hCapacity : store.mem.read64 (block.root - 32).toUInt32 = block.capacity)
    (hApart : ∀ n ∈ rest, regionsDisjoint block.region n.region)
    (Q : Assertion Unit) (after : Program)
    (hNext : wp m after Q { store with mem := joinMem store.mem block rest } s env) :
    wp m (joinProgram ptrLocal nextLocal ++ after) Q store s env := by
  have hEmpty : { s with values := [] } = s := Project.ProofKit.Frame.ext _ _ rfl rfl hValues.symm
  have hMod (r k : UInt64) (hk : k.toNat ≤ 48) (h48 : 48 ≤ r.toNat) (h32 : r.toNat < 4294967296) :
      (r - k).toNat % 4294967296 = r.toNat - k.toNat := by
    rw [Project.Common.toNat_sub_le _ _ (by omega), Nat.mod_eq_of_lt (by omega)]
  have hA (r k : UInt64) (hk : k.toNat ≤ 48) (h48 : 48 ≤ r.toNat) (h32 : r.toNat < 4294967296) :
      (r - k).toUInt32 = UInt32.ofNat (r.toNat - k.toNat) := by
    rw [Memory.toUInt32_eq_ofNat, hMod r k hk h48 h32]
  have hb32 := hMod block.root 32 (by decide) h48 (by omega)
  have hb8 := hMod block.root 8 (by decide) h48 (by omega)
  have hAb32 := hA block.root 32 (by decide) h48 (by omega)
  have hAb8 := hA block.root 8 (by decide) h48 (by omega)
  simp only [UInt64.reduceToNat] at hb32 hb8 hAb32 hAb8
  have hc32 : ¬ store.mem.pages * 65536 < block.root.toNat - 32 + 8 := by omega
  have hc8 : ¬ store.mem.pages * 65536 < block.root.toNat - 8 + 8 := by omega
  have hCap : store.mem.read64 (UInt32.ofNat (block.root.toNat - 32)) = block.capacity := by
    rw [← hAb32]
    exact hCapacity
  simp only [joinProgram, headerLoad, headerStore, List.cons_append, List.nil_append,
    List.append_assoc]
  have hm32 : (block.root.toNat - 32) % 4294967296 = block.root.toNat - 32 :=
    Nat.mod_eq_of_lt (by omega)
  have hm8 : (block.root.toNat - 8) % 4294967296 = block.root.toNat - 8 :=
    Nat.mod_eq_of_lt (by omega)
  simp [-Locals.get, wp_simp, hPtr, hNextLocal, hValues, hb32, hm32, hc32, hCap]
  refine wp_iff_cons rfl ?_
  cases rest with
  | nil =>
    have hNe : ¬ block.root + block.capacity + 48 = 0 := by
      intro h
      have := congrArg UInt64.toNat h
      rw [UInt64.toNat_add, UInt64.toNat_add] at this
      simp only [UInt64.reduceToNat] at this
      omega
    simp [-Locals.get, wp_simp, hNe, hPtr, hNextLocal, hb8, hm8, hc8, freeHead]
    simpa [joinMem, hAb8, hEmpty] using hNext
  | cons next tail =>
    cases hRest with
    | cons hn48 hn32 hnFit hnRc hnCapacity hnLink hnSep hnTail =>
      have hn32' := hMod next.root 32 (by decide) hn48 (by omega)
      have hn8 := hMod next.root 8 (by decide) hn48 (by omega)
      have hAn32 := hA next.root 32 (by decide) hn48 (by omega)
      have hAn8 := hA next.root 8 (by decide) hn48 (by omega)
      simp only [UInt64.reduceToNat] at hn32' hn8 hAn32 hAn8
      have hnm32 : (next.root.toNat - 32) % 4294967296 = next.root.toNat - 32 :=
        Nat.mod_eq_of_lt (by omega)
      have hnm8 : (next.root.toNat - 8) % 4294967296 = next.root.toNat - 8 :=
        Nat.mod_eq_of_lt (by omega)
      by_cases hAdj : block.root + block.capacity + 48 = next.root
      · have hAdjN := adjoins_toNat h32 hAdj
        have hnc32 : ¬ store.mem.pages * 65536 < next.root.toNat - 32 + 8 := by omega
        have hnc8 : ¬ store.mem.pages * 65536 < next.root.toNat - 8 + 8 := by omega
        have hnCap : store.mem.read64 (UInt32.ofNat (next.root.toNat - 32)) = next.capacity := by
          rw [← hAn32]
          exact hnCapacity
        have hnLink' : ∀ v, (store.mem.write64 (UInt32.ofNat (block.root.toNat - 32)) v).read64
            (UInt32.ofNat (next.root.toNat - 8)) = freeHead tail := fun v => by
          rw [Memory.read64_write64_disjoint _ _ _ _ (by
            simp only [UInt32.toNat_ofNat', Nat.reducePow, Nat.mod_eq_of_lt (show next.root.toNat - 8 < 4294967296 by omega),
              Nat.mod_eq_of_lt (show block.root.toNat - 32 < 4294967296 by omega)]
            omega), ← hAn8]
          exact hnLink
        simp [-Locals.get, wp_simp, hAdj, hPtr, hNextLocal, freeHead,
          hb32, hm32, hc32, hb8, hm8, hc8, hCap, hn32', hnm32, hnc32, hn8, hnm8, hnc8, hnCap, hnLink',
          Wasm.Mem.write64_pages]
        simpa [joinMem, hAdj, hAb32, hAb8, hEmpty, freeHead] using hNext
      · simp [-Locals.get, wp_simp, hAdj, hPtr, hNextLocal, freeHead, hb8, hm8, hc8]
        simpa [joinMem, hAdj, hAb8, hEmpty] using hNext

/-- `findPlace` walks the free list to the first block above `ptr`, leaving the
last block at or below it in `releasePrevious` and that first block in
`releaseCurrent`. -/
theorem findPlace_spec {m : Module} (env : HostEnv Unit) (store : Store Unit)
    (nodes : List FreeNode) (ptr pending previous current : UInt64)
    (hList : FreeListAt store.mem nodes)
    (hHead : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (Q : Assertion Unit) (after : Program)
    (hNext : wp m after Q store (releaseLocals ptr pending ptr
      (previousRoot 0 (belowNodes ptr nodes)) (freeHead (aboveNodes ptr nodes))) env) :
    wp m (findPlace ++ after) Q store (releaseLocals ptr pending ptr previous current) env := by
  obtain ⟨hHeadLength, hHeadRead⟩ := List.getElem_of_getElem? hHead
  simp only [findPlace, headerLoad, List.cons_append, List.nil_append]
  simp [wp_simp, releaseLocals, releasePrevious, releaseCurrent, hHeadLength, hHeadRead]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st s => st = store ∧ ∃ visited remaining, nodes = visited ++ remaining ∧
      (∀ n ∈ visited, n.root ≤ ptr) ∧
      s = releaseLocals ptr pending ptr (previousRoot 0 visited) (freeHead remaining))
    (μ := fun _ s => match s.get releaseCurrent with
      | some (.i64 c) => scanRemaining nodes c
      | _ => 0)
  · exact ⟨rfl, [], nodes, rfl, by simp, rfl⟩
  · rintro st s ⟨hst, visited, remaining, hSplit, hVisited, rfl⟩
    subst st
    cases remaining with
    | nil =>
      obtain ⟨hBelow, hAbove⟩ := belowNodes_append (root := ptr) (remaining := [])
        hVisited (by simp)
      simp only [List.append_nil] at hBelow hAbove
      rw [hSplit, List.append_nil] at hNext
      simp [wp_simp, releaseLocals, releaseCurrent, freeHead]
      simpa [hBelow, hAbove, releaseLocals, freeHead] using hNext
    | cons n rest =>
      have hSuffix : FreeListAt store.mem (n :: rest) := by
        rw [hSplit] at hList
        exact hList.suffix
      cases hSuffix with
      | cons hn48 hn32 hnFit hnRc hnCapacity hnLink hnSep hnTail =>
        have hRoot : n.root ≠ 0 := by
          intro h
          have := congrArg UInt64.toNat h
          simp at this
          omega
        by_cases hLt : ptr < n.root
        · obtain ⟨hBelow, hAbove⟩ := belowNodes_append (root := ptr) (remaining := n :: rest)
            hVisited (fun n' h => by simp at h; subst h; exact hLt)
          rw [hSplit] at hNext
          simp [wp_simp, releaseLocals, releaseCurrent, releaseObject, freeHead, hRoot, hLt]
          simpa [hBelow, hAbove, releaseLocals, freeHead] using hNext
        · have hn8 : (n.root - 8).toNat % 4294967296 = n.root.toNat - 8 := by
            rw [Project.Common.toNat_sub_le _ _ (by simp; omega), Nat.mod_eq_of_lt (by simp; omega)]
            rfl
          have hnm8 : (n.root.toNat - 8) % 4294967296 = n.root.toNat - 8 :=
            Nat.mod_eq_of_lt (by omega)
          have hnc8 : ¬ store.mem.pages * 65536 < n.root.toNat - 8 + 8 := by omega
          have hLink : store.mem.read64 (UInt32.ofNat (n.root.toNat - 8)) = freeHead rest := by
            rw [← hnLink, Memory.toUInt32_eq_ofNat, hn8]
          have hScanBefore := hList.scanRemaining_suffix (visited := visited)
            (remaining := n :: rest) hSplit
          have hScanAfter := hList.scanRemaining_suffix (visited := visited ++ [n])
            (remaining := rest) (by rw [hSplit]; simp)
          simp only [freeHead, List.length_cons] at hScanBefore
          simp [wp_simp, releaseLocals, releaseCurrent, releaseObject, releasePrevious, freeHead,
            hRoot, hLt, hn8, hnm8, hnc8, hLink]
          refine ⟨⟨visited ++ [n], rest, by rw [hSplit]; simp, ?_, ?_⟩, ?_⟩
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hVisited x hx
            · simp only [List.mem_singleton] at hx
              subst hx
              rw [UInt64.le_iff_toNat_le]
              rw [UInt64.lt_iff_toNat_lt] at hLt
              omega
          · simp [releaseLocals, previousRoot_append_singleton]
          · simp only [freeHead] at hScanAfter
            omega

/-- The store `release` reaches after dropping the last reference to the object
at `ptr`: the count word cleared and the release counted. -/
def releaseEntry (heap : Heap) (store : Store Unit) (ptr : UInt64) : Store Unit :=
  { store with
    globals := { globals := [.i64 heap.top, .i64 (freeHead heap.free), .i64 heap.allocs,
      .i64 heap.retains, .i64 (heap.releases + 1), .i64 heap.frees] }
    mem := store.mem.write64 (UInt32.ofNat (ptr.toNat - 40)) 0 }

/-- `freeObject` returns the block of an owned object to the free list, as
`Heap.releaseStore` describes. -/
theorem freeObject_spec {m : Module} (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (ptr : UInt64) (words : Array UInt64) (hHeap : heap.At store)
    (hOwned : heap.Owned store ptr words) (Q : Assertion Unit) (after : Program)
    (hNext : ∀ previous current, wp m after Q (heap.releaseStore store ptr)
      (releaseLocals ptr 0 ptr previous current) env) :
    wp m (freeObject ++ after) Q (releaseEntry heap store ptr) (releaseLocals ptr 0 ptr 0 0) env := by
  set capacity := store.mem.read64 (ptr - 32).toUInt32 with hCapacityDef
  have hBase := hOwned.base
  have hAddress := hOwned.address
  have hBelow := hOwned.below
  have hTop := hHeap.top
  have hSeparate := hOwned.separate
  simp only [capacityAt] at hAddress hBelow hSeparate
  rw [← hCapacityDef] at hAddress hBelow hSeparate
  have hA (k : UInt64) (hk : k.toNat ≤ 48) :
      (ptr - k).toUInt32 = UInt32.ofNat (ptr.toNat - k.toNat) := by
    rw [Memory.toUInt32_eq_ofNat, Project.Common.toNat_sub_le _ _ (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hA40 := hA 40 (by decide)
  have hA32 := hA 32 (by decide)
  simp only [UInt64.reduceToNat] at hA40 hA32
  have hs40 : (ptr - 40).toNat % 4294967296 = ptr.toNat - 40 := by
    rw [Project.Common.toNat_sub_le _ _ (by simp; omega), Nat.mod_eq_of_lt (by simp; omega)]
    rfl
  have hm40 : (ptr.toNat - 40) % 4294967296 = ptr.toNat - 40 := Nat.mod_eq_of_lt (by omega)
  have hc40 : ¬ store.mem.pages * 65536 < ptr.toNat - 40 + 8 := by omega
  -- The store after the free counter and the second write of the count word.
  set mem1 := (store.mem.write64 (UInt32.ofNat (ptr.toNat - 40)) 0).write64
    (UInt32.ofNat (ptr.toNat - 40)) 0 with hMem1
  have hw40 : (UInt32.ofNat (ptr.toNat - 40)).toNat = ptr.toNat - 40 := by
    simp only [UInt32.toNat_ofNat', Nat.reducePow, hm40]
  have hw32 : (UInt32.ofNat (ptr.toNat - 32)).toNat = ptr.toNat - 32 := by
    simp only [UInt32.toNat_ofNat', Nat.reducePow]
    exact Nat.mod_eq_of_lt (by omega)
  have hBytes1 : ∀ a, a < ptr.toNat - 48 ∨ ptr.toNat ≤ a → mem1.bytes a = store.mem.bytes a :=
    fun a ha => by
      rw [hMem1, Memory.write64_bytes_outside _ _ _ (by rw [hw40]; omega),
        Memory.write64_bytes_outside _ _ _ (by rw [hw40]; omega)]
  have hFree : ∀ n ∈ heap.free, ∀ a, n.root.toNat - 48 ≤ a → a < n.root.toNat →
      a < ptr.toNat - 48 ∨ ptr.toNat ≤ a := fun n hn a hLow hHigh => by
    have := hSeparate n hn
    simp only [regionsDisjoint, FreeNode.region] at this
    omega
  have hList1 : FreeListAt mem1 heap.free :=
    FreeListMemory.frame_headers hHeap.freeList (by simp [hMem1, Wasm.Mem.write64_pages])
      fun n hn a hLow hHigh => hBytes1 a (hFree n hn a hLow hHigh)
  have hCapacity1 : mem1.read64 (ptr - 32).toUInt32 = capacity := by
    rw [hA32, hMem1, Memory.read64_write64_disjoint _ _ _ _ (by rw [hw40, hw32]; omega),
      Memory.read64_write64_disjoint _ _ _ _ (by rw [hw40, hw32]; omega), ← hA32]
  have hPages1 : mem1.pages = store.mem.pages := by simp [hMem1, Wasm.Mem.write64_pages]
  have hSplit := nodes_split ptr heap.free
  have hAboveMem : ∀ n ∈ aboveNodes ptr heap.free, n ∈ heap.free := fun n hn => by
    rw [hSplit]
    exact List.mem_append_right _ hn
  have hAbove1 : FreeListAt mem1 (aboveNodes ptr heap.free) := by
    have h' := hList1
    rw [hSplit] at h'
    exact h'.suffix
  have hApartQ : ∀ n ∈ aboveNodes ptr heap.free,
      regionsDisjoint (FreeNode.region { root := ptr, capacity }) n.region :=
    fun n hn => regionsDisjoint_symm (hSeparate n (hAboveMem n hn))
  simp only [freeObject, incrementGlobal, headerStore, releaseObject, List.cons_append,
    List.nil_append, List.append_assoc]
  simp [wp_simp, releaseEntry, releaseLocals, hs40, hm40, hc40]
  refine findPlace_spec env _ heap.free ptr 0 0 0 (by simpa [hMem1] using hList1) (by simp) _ _ ?_
  refine joinProgram_spec env _ _ releaseObject releaseCurrent { root := ptr, capacity }
    (aboveNodes ptr heap.free) rfl (by simp [releaseLocals, releaseObject])
    (by simp [releaseLocals, releaseCurrent]) (by simpa [hMem1] using hAbove1) (by simp; omega)
    (by simp; omega) (by simp [Wasm.Mem.write64_pages]; omega)
    (by simpa [hMem1] using hCapacity1) hApartQ _ _ ?_
  set mem2 := joinMem mem1 { root := ptr, capacity } (aboveNodes ptr heap.free) with hMem2
  have hBlock : FreeListAt mem2 (joinNodes { root := ptr, capacity } (aboveNodes ptr heap.free)) :=
    FreeListAt.join hAbove1 (by simp; omega) (by simp; omega) (by rw [hPages1]; simp; omega)
      (by
        show mem1.read64 (ptr - 40).toUInt32 = 0
        rw [hA40, hMem1]
        exact Memory.read64_write64 _ _ _)
      hCapacity1 hApartQ
  simp [wp_simp, releaseLocals, releasePrevious]
  refine wp_iff_cons rfl ?_
  have hGlobals : (heap.release ptr capacity).globals =
      [.i64 heap.top, .i64 (if belowNodes ptr heap.free = [] then ptr else freeHead heap.free),
        .i64 heap.allocs, .i64 heap.retains, .i64 (heap.releases + 1), .i64 (heap.frees + 1)] := by
    simp [Heap.release, Heap.globals, freeHead_insertFree]
  cases hLast : (belowNodes ptr heap.free).getLast? with
  | none =>
    have hNil : belowNodes ptr heap.free = [] := List.getLast?_eq_none_iff.mp hLast
    have hStore : { releaseEntry heap store ptr with
        globals := { globals := [.i64 heap.top, .i64 ptr, .i64 heap.allocs, .i64 heap.retains,
          .i64 (heap.releases + 1), .i64 (heap.frees + 1)] }
        mem := mem2 } = heap.releaseStore store ptr := by
      simp only [releaseEntry, Heap.releaseStore]
      congr 1
      · rw [hGlobals]
        simp [hNil]
      · simp only [releaseMem, hLast, hMem2, hMem1, hA40, ← hCapacityDef]
    simp [hNil, previousRoot, wp_simp, releaseObject]
    have h := hNext 0 (freeHead (aboveNodes ptr heap.free))
    rw [← hStore] at h
    exact h
  | some p =>
    obtain ⟨pre, hPre⟩ := List.getLast?_eq_some_iff.mp hLast
    have hPrevious : previousRoot 0 (belowNodes ptr heap.free) = p.root := by
      rw [hPre, previousRoot_append_singleton]
    have hp : p ∈ heap.free := by
      rw [hSplit]
      exact List.mem_append_left _ (List.mem_of_getLast? hLast)
    obtain ⟨hp48, hp32, hpFit⟩ := hHeap.freeList.mem_bounds hp
    have hpRoot : p.root ≠ 0 := hHeap.freeList.roots_ne_zero p hp
    have hpq := hSeparate p hp
    simp only [regionsDisjoint, FreeNode.region] at hpq
    have hPair := hHeap.freeList.pairwise
    rw [hSplit, List.pairwise_append] at hPair
    have hpAbove : ∀ n ∈ aboveNodes ptr heap.free, regionsDisjoint p.region n.region :=
      fun n hn => hPair.2.2 p (List.mem_of_getLast? hLast) n hn
    have hBytes2 : ∀ a, p.root.toNat - 48 ≤ a → a < p.root.toNat → mem2.bytes a =
        store.mem.bytes a := fun a hLow hHigh => by
      rw [hMem2, joinMem_bytes (block := { root := ptr, capacity }) _ _ (by simp; omega)
        (by simp; omega) (by simp; omega)]
      exact hBytes1 a (by omega)
    have hpHeader := hHeap.freeList.header hp
    have hpCapacity : mem2.read64 (p.root - 32).toUInt32 = p.capacity :=
      (read64_header (by decide) (by decide) hp48 (by omega) hBytes2).trans hpHeader.2
    have hNe : belowNodes ptr heap.free ≠ [] := by simp [hPre]
    have hStore : { releaseEntry heap store ptr with
        globals := { globals := [.i64 heap.top, .i64 (freeHead heap.free), .i64 heap.allocs,
          .i64 heap.retains, .i64 (heap.releases + 1), .i64 (heap.frees + 1)] }
        mem := joinMem mem2 p (joinNodes { root := ptr, capacity } (aboveNodes ptr heap.free)) } =
        heap.releaseStore store ptr := by
      simp only [releaseEntry, Heap.releaseStore]
      congr 1
      · rw [hGlobals]
        simp [hNe]
      · simp only [releaseMem, hLast, hMem2, hMem1, hA40, ← hCapacityDef]
    simp only [hPrevious, hpRoot, if_false, ne_eq, not_true_eq_false, ite_false]
    have hpFit2 : p.root.toNat + p.capacity.toNat ≤ mem2.pages * 65536 := by
      rw [hMem2, joinMem_pages, hPages1]
      omega
    rw [← List.append_nil (joinProgram 11 3)]
    refine joinProgram_spec env _ _ releasePrevious releaseObject p
      (joinNodes { root := ptr, capacity } (aboveNodes ptr heap.free)) rfl ?_ ?_ ?_ hp48 hp32
      ?_ ?_ ?_ _ _ ?_
    · simp [releaseLocals, releasePrevious, hPrevious]
    · simp [releaseLocals, releaseObject, freeHead_joinNodes]
    · exact hBlock
    · exact hpFit2
    · exact hpCapacity
    · exact joinNodes_apart (block := { root := ptr, capacity }) (by simp; omega)
        (by simp; omega)
        (fun n hn => ⟨(hHeap.freeList.mem_bounds (hAboveMem n hn)).1,
          (hHeap.freeList.mem_bounds (hAboveMem n hn)).2.1⟩)
        (by simp only [FreeNode.region]; omega)
        (by simp only [regionsDisjoint, FreeNode.region]; omega) hpAbove
    have h := hNext p.root (freeHead (aboveNodes ptr heap.free))
    rw [← hStore] at h
    simp [wp_simp]
    exact h

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
  have hMagic : store.mem.read64 (UInt32.ofNat (ptr.toNat - 48)) = magic := by
    rw [← hA48]; exact hOwned.magic
  have hCount : store.mem.read64 (UInt32.ofNat (ptr.toNat - 40)) = 1 := by
    rw [← hA40]; exact hOwned.count
  have hMask : (store.mem.write64 (UInt32.ofNat (ptr.toNat - 40)) 0).read64
      (UInt32.ofNat (ptr.toNat - 8)) = 0 := by
    rw [← hA40, ← hA8,
      Memory.read64_write64_disjoint _ _ _ _ (by
        rw [headerAddress_toNat (by simp; omega) (by omega),
          headerAddress_toNat (by simp; omega) (by omega)]
        simp only [UInt64.reduceToNat]
        omega)]
    exact hOwned.childMask
  have hGlobals := hHeap.globals
  have hb48 : ptr.toNat - 48 + 8 ≤ store.mem.pages * 65536 := by omega
  have hb40 : ptr.toNat - 40 + 8 ≤ store.mem.pages * 65536 := by omega
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
  change wp m _ _ _ (releaseLocals ptr ptr 0 0 0) env
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st s => (st = releaseEntry heap store ptr ∧ s = releaseLocals ptr ptr 0 0 0) ∨
      (st = heap.releaseStore store ptr ∧ ∃ previous current,
        s = releaseLocals ptr 0 ptr previous current))
    (fun _ s => match s.get releasePending with
      | some (.i64 pending) => pending.toNat
      | _ => 0) (Or.inl ⟨rfl, rfl⟩) ?_
  rintro st s (⟨rfl, rfl⟩ | ⟨rfl, previous, current, rfl⟩)
  · simp only [releaseLocals, wp_simp, releasePending]
    simp only [Locals.get, Locals.set?]
    simp [releaseEntry, hs40, hm40, hc40, hPtr]
    simp only [dropChildren, headerLoad, releaseMask, releaseObject, List.cons_append,
      List.nil_append, wp_simp]
    simp only [Locals.get, Locals.set?]
    simp [hs8, hm8, hc8, hMask]
    refine wp_iff_cons rfl ?_
    simp only [ite_true, ne_eq, not_true_eq_false, ite_false, List.nil_append, wp_nil]
    change wp m (freeObject ++ [.br 0]) _ (releaseEntry heap store ptr)
      (releaseLocals ptr 0 ptr 0 0) env
    refine freeObject_spec env heap store ptr words hHeap hOwned _ _ fun previous current => ?_
    simp [wp_simp, releaseLocals, releasePending]
    omega
  · simp [releaseLocals, wp_simp]

/-- `release` changes no byte outside the header of the freed object and the
headers of free blocks. -/
theorem Heap.releaseStore_bytes {heap : Heap} {store : Store Unit} {ptr : UInt64}
    (hHeap : heap.At store) (hBase : 48 ≤ ptr.toNat) (hFit : ptr.toNat < 4294967296)
    {address : Nat} (h : address < ptr.toNat - 48 ∨ ptr.toNat ≤ address)
    (hFree : ∀ node ∈ heap.free, address < node.root.toNat - 48 ∨ node.root.toNat ≤ address) :
    (heap.releaseStore store ptr).mem.bytes address = store.mem.bytes address := by
  have h40 := headerAddress_toNat (ptr := ptr) (k := 40) (by simp; omega) hFit
  simp only [UInt64.reduceToNat] at h40
  simp only [Heap.releaseStore]
  rw [releaseMem_bytes _ hBase hFit (fun n hn => ⟨(hHeap.freeList.mem_bounds hn).1, by
      have := (hHeap.freeList.mem_bounds hn).2.1
      omega⟩) h hFree,
    Memory.write64_bytes_outside _ _ _ (by omega)]

theorem Heap.releaseStore_pages (heap : Heap) (store : Store Unit) (ptr : UInt64) :
    (heap.releaseStore store ptr).mem.pages = store.mem.pages := by
  simp only [Heap.releaseStore, releaseMem_pages, Wasm.Mem.write64_pages]

theorem Heap.At.free_bounds {heap : Heap} {store : Store Unit} (hHeap : heap.At store) :
    ∀ n ∈ heap.free, 48 ≤ n.root.toNat ∧ n.root.toNat + n.capacity.toNat < 4294967296 :=
  fun n hn => ⟨(hHeap.freeList.mem_bounds hn).1, (hHeap.freeList.mem_bounds hn).2.1⟩

/-- An array borrowed outside a freed object stays borrowed after the release. -/
theorem Heap.Borrowed.release {heap : Heap} {store : Store Unit} {p q : UInt64}
    {ws qs : Array UInt64} (h : heap.Borrowed store p ws) (hHeap : heap.At store)
    (hOwned : heap.Owned store q qs)
    (hDisjoint : regionsDisjoint (p.toNat, 8 * (ws.size + 1))
      (q.toNat - 48, 48 + capacityAt store q)) :
    (heap.release q (store.mem.read64 (q - 32).toUInt32)).Borrowed (heap.releaseStore store q) p
      ws := by
  have hBase := hOwned.base
  have hFit := hOwned.address
  simp only [capacityAt] at hFit hDisjoint
  refine ⟨arrayAt_frame h.values (by rw [Heap.releaseStore_pages]) fun address hLow hHigh => ?_,
    h.below, ?_⟩
  · refine Heap.releaseStore_bytes hHeap (by omega) (by omega) (by
      unfold regionsDisjoint at hDisjoint
      omega) fun node hn => ?_
    have hSep := h.separate node hn
    have := (hHeap.freeList.mem_bounds hn).1
    simp only [regionsDisjoint, FreeNode.region] at hSep
    omega
  · exact insertFree_apart (by omega) (by omega) hHeap.free_bounds (by simp only; omega)
      hDisjoint h.separate

/-- An object owned outside a freed object stays owned after the release, with its
capacity word unchanged. -/
theorem Heap.Owned.release {heap : Heap} {store : Store Unit} {p q : UInt64}
    {ws qs : Array UInt64} (h : heap.Owned store p ws) (hHeap : heap.At store)
    (hOwned : heap.Owned store q qs)
    (hDisjoint : regionsDisjoint (p.toNat - 48, 48 + capacityAt store p)
      (q.toNat - 48, 48 + capacityAt store q)) :
    (heap.release q (store.mem.read64 (q - 32).toUInt32)).Owned (heap.releaseStore store q) p ws ∧
      capacityAt (heap.releaseStore store q) p = capacityAt store p := by
  have hBase := hOwned.base
  have hFit := hOwned.address
  have hpBase := h.base
  have hpFit := h.address
  have hBytes : ∀ address, p.toNat - 48 ≤ address → address < p.toNat + capacityAt store p →
      (heap.releaseStore store q).mem.bytes address = store.mem.bytes address :=
    fun address hLow hHigh => by
      refine Heap.releaseStore_bytes hHeap (by omega) (by simp only [capacityAt] at hFit; omega)
        (by unfold regionsDisjoint at hDisjoint; omega) fun node hn => ?_
      have hSep := h.separate node hn
      have := (hHeap.freeList.mem_bounds hn).1
      simp only [regionsDisjoint, FreeNode.region] at hSep
      omega
  refine ⟨h.frame (by rw [Heap.releaseStore_pages]) hBytes h.below ?_,
    capacityAt_frame (by omega) (by omega) fun a hl hh => hBytes a hl (by omega)⟩
  intro node hNode
  simp only [capacityAt] at hFit hDisjoint
  refine regionsDisjoint_symm (insertFree_apart (by omega) (by omega) hHeap.free_bounds
    (by simp only; omega) hDisjoint (fun n hn => regionsDisjoint_symm (h.separate n hn)) node ?_)
  exact hNode

/-- Freeing an owned array keeps the allocator invariant, with the object's block
inserted in the free list. -/
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
  simp only [UInt64.reduceToNat] at h40 h32
  have hTop := hHeap.top
  have hPagesMax := hHeap.pages
  have hq32 : ptr.toNat + (store.mem.read64 (ptr - 32).toUInt32).toNat < 4294967296 := hFit
  have hCover := insertFree_cover (nodes := heap.free) hq32 fun n hn => (hHeap.free_bounds n hn).2
  refine ⟨rfl, ?_, hHeap.base, by rw [Heap.releaseStore_pages]; exact hTop,
    by rw [Heap.releaseStore_pages]; exact hPagesMax, ?_, ?_⟩
  · simp only [Heap.releaseStore, Heap.release]
    refine FreeListAt.release ?_ (by omega) (by omega)
      (by simp only [Wasm.Mem.write64_pages]; omega)
      (by rw [Memory.read64_write64_disjoint _ _ _ _ (by omega)]) fun n hn =>
        regionsDisjoint_symm (hSeparate n hn)
    refine FreeListMemory.frame_headers hHeap.freeList (by simp [Wasm.Mem.write64_pages])
      fun node hNode address hLow hHigh => Memory.write64_bytes_outside _ _ _ ?_
    have hNodeSeparate := hSeparate node hNode
    have := hHeap.above node hNode
    simp only [regionsDisjoint, FreeNode.region] at hNodeSeparate
    omega
  · intro node hNode
    rcases (hCover node hNode).1 with h | ⟨m, hm, h⟩
    · rw [h]
      exact hBase
    · rw [h]
      exact hHeap.above m hm
  · intro node hNode
    show node.root.toNat + node.capacity.toNat ≤ heap.top.toNat
    rcases (hCover node hNode).2 with h | ⟨m, hm, h⟩
    · omega
    · have := hHeap.below m hm
      omega

end Project.Pipeline
