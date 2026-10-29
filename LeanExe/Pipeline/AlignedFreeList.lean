import LeanExe.Pipeline.AlignedHeap
import LeanExe.Pipeline.AlignedRuns
import LeanExe.ProofKit.AlignedTransfer

/-!
The return of a block to the free list by `release`, under `wpA`: the ports of
`joinProgram_spec`, `findPlace_spec`, `freeObject_spec`, and `release_leaf_run`.  The program reads
and writes the size and link words of the freed block, at its payload pointer minus 32 and minus
8, and of the free blocks around its place, and clears the freed object's count word at its
pointer minus 40.  `release_leaf_runA` also reads the object's magic number, count, and child
mask, at its pointer minus 48, 40, and 8.  Every access is aligned when the pointer and the roots
of the free blocks are multiples of 8.  `release_null_runA` is the call on the null pointer,
which returns before any access.
-/

namespace LeanExe.Pipeline

open Wasm LeanExe.Runtime LeanExe.ProofKit

attribute [-simp] Wasm.Mem.read64_write64_same
attribute [local simp] Memory.read64_write64

/-- A block of `joinNodes block rest` has the root of `block` or is a block of `rest`. -/
theorem joinNodes_root {block n : FreeNode} {rest : List FreeNode}
    (h : n ∈ joinNodes block rest) : n.root = block.root ∨ n ∈ rest := by
  cases rest with
  | nil => simp only [joinNodes, List.mem_singleton] at h; exact .inl (by rw [h])
  | cons next tail =>
    simp only [joinNodes] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact .inl rfl
      · exact .inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact .inl rfl
      · exact .inr h

theorem joinProgram_specA {m : Module} (env : HostEnv Unit) (store : Store Unit) (s : Locals)
    (ptrLocal nextLocal : Nat) (block : FreeNode) (rest : List FreeNode)
    (hValues : s.values = []) (hPtr : s.get ptrLocal = some (.i64 block.root))
    (hNextLocal : s.get nextLocal = some (.i64 (freeHead rest)))
    (hRest : FreeListAt store.mem rest) (h48 : 48 ≤ block.root.toNat)
    (h32 : block.root.toNat + block.capacity.toNat < 4294967296)
    (hFit : block.root.toNat + block.capacity.toNat ≤ store.mem.pages * 65536)
    (hCapacity : store.mem.read64 (block.root - 32).toUInt32 = block.capacity)
    (hApart : ∀ n ∈ rest, regionsDisjoint block.region n.region)
    (hRootAl : block.root.toNat % 8 = 0) (hRestAl : ∀ n ∈ rest, n.root.toNat % 8 = 0)
    (Q : Assertion Unit) (after : Program)
    (hNext : wpA m after Q { store with mem := joinMem store.mem block rest } s env) :
    wpA m (joinProgram ptrLocal nextLocal ++ after) Q store s env := by
  have hEmpty : { s with values := [] } = s := LeanExe.ProofKit.Frame.ext _ _ rfl rfl hValues.symm
  have hMod (r k : UInt64) (hk : k.toNat ≤ 48) (h48 : 48 ≤ r.toNat) (h32 : r.toNat < 4294967296) :
      (r - k).toNat % 4294967296 = r.toNat - k.toNat := by
    rw [LeanExe.Common.toNat_sub_le _ _ (by omega), Nat.mod_eq_of_lt (by omega)]
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
  simp only [joinProgram, headerLoad, headerStore, List.cons_append, List.nil_append]
  have hm32 : (block.root.toNat - 32) % 4294967296 = block.root.toNat - 32 :=
    Nat.mod_eq_of_lt (by omega)
  have hm8 : (block.root.toNat - 8) % 4294967296 = block.root.toNat - 8 :=
    Nat.mod_eq_of_lt (by omega)
  have hab32 : (block.root.toNat - 32) % 8 = 0 := by omega
  have hab8 : (block.root.toNat - 8) % 8 = 0 := by omega
  simp [-Locals.get, wpA_simp, wp_simp, hPtr, hNextLocal, hValues, hb32, hm32, hc32, hCap, hab32]
  refine wpA_iff_cons rfl ?_
  cases rest with
  | nil =>
    have hNe : ¬ block.root + block.capacity + 48 = 0 := by
      intro h
      have := congrArg UInt64.toNat h
      rw [UInt64.toNat_add, UInt64.toNat_add] at this
      simp only [UInt64.reduceToNat] at this
      omega
    simp [-Locals.get, wpA_simp, wp_simp, hNe, hPtr, hNextLocal, hb8, hm8, hc8, hab8, freeHead]
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
      have hnAl := hRestAl next List.mem_cons_self
      have han32 : (next.root.toNat - 32) % 8 = 0 := by omega
      have han8 : (next.root.toNat - 8) % 8 = 0 := by omega
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
        simp [-Locals.get, wpA_simp, wp_simp, hAdj, hPtr, hNextLocal, freeHead,
          hb32, hm32, hc32, hb8, hm8, hc8, hCap, hn32', hnm32, hnc32, hn8, hnm8, hnc8, hnCap, hnLink',
          Wasm.Mem.write64_pages, hab32, hab8, han32, han8]
        simpa [joinMem, hAdj, hAb32, hAb8, hEmpty, freeHead] using hNext
      · simp [-Locals.get, wpA_simp, wp_simp, hAdj, hPtr, hNextLocal, freeHead, hb8, hm8, hc8, hab8]
        simpa [joinMem, hAdj, hAb8, hEmpty] using hNext

theorem findPlace_specA {m : Module} (env : HostEnv Unit) (store : Store Unit)
    (nodes : List FreeNode) (v : ReleaseVars)
    (hList : FreeListAt store.mem nodes)
    (hHead : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hRoots : ∀ n ∈ nodes, n.root.toNat % 8 = 0)
    (Q : Assertion Unit) (after : Program)
    (hNext : wpA m after Q store (v.atPlace (previousRoot 0 (belowNodes v.object nodes))
      (freeHead (aboveNodes v.object nodes))).toLocals env) :
    wpA m (findPlace ++ after) Q store v.toLocals env := by
  obtain ⟨hHeadLength, hHeadRead⟩ := List.getElem_of_getElem? hHead
  obtain ⟨root, count, pending, ptr, kind, length, width, mask, element, slot, child, previous0,
    current0⟩ := v
  simp only [ReleaseVars.atPlace] at hNext
  simp only [findPlace, headerLoad, List.cons_append, List.nil_append]
  simp [wpA_simp, wp_simp, ReleaseVars.toLocals, releasePrevious, releaseCurrent, hHeadLength, hHeadRead]
  apply wpA_block_cons
  apply wpA_loop_cons
    (Inv := fun st s => st = store ∧ ∃ visited remaining, nodes = visited ++ remaining ∧
      (∀ n ∈ visited, n.root ≤ ptr) ∧
      s = ReleaseVars.toLocals ⟨root, count, pending, ptr, kind, length, width, mask, element,
        slot, child, previousRoot 0 visited, freeHead remaining⟩)
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
      simp [wpA_simp, wp_simp, ReleaseVars.toLocals, releaseCurrent, freeHead]
      simpa [hBelow, hAbove, ReleaseVars.toLocals, freeHead] using hNext
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
          simp [wpA_simp, wp_simp, ReleaseVars.toLocals, releaseCurrent, releaseObject, freeHead, hRoot, hLt]
          simpa [hBelow, hAbove, ReleaseVars.toLocals, freeHead] using hNext
        · have hn8 : (n.root - 8).toNat % 4294967296 = n.root.toNat - 8 := by
            rw [LeanExe.Common.toNat_sub_le _ _ (by simp; omega), Nat.mod_eq_of_lt (by simp; omega)]
            rfl
          have hnm8 : (n.root.toNat - 8) % 4294967296 = n.root.toNat - 8 :=
            Nat.mod_eq_of_lt (by omega)
          have hnc8 : ¬ store.mem.pages * 65536 < n.root.toNat - 8 + 8 := by omega
          have hnAl := hRoots n (by rw [hSplit]; simp)
          have hna8 : (n.root.toNat - 8) % 8 = 0 := by omega
          have hLink : store.mem.read64 (UInt32.ofNat (n.root.toNat - 8)) = freeHead rest := by
            rw [← hnLink, Memory.toUInt32_eq_ofNat, hn8]
          have hScanBefore := hList.scanRemaining_suffix (visited := visited)
            (remaining := n :: rest) hSplit
          have hScanAfter := hList.scanRemaining_suffix (visited := visited ++ [n])
            (remaining := rest) (by rw [hSplit]; simp)
          simp only [freeHead, List.length_cons] at hScanBefore
          simp [wpA_simp, wp_simp, ReleaseVars.toLocals, releaseCurrent, releaseObject, freeHead,
            hRoot, hLt, hn8, hnm8, hnc8, hna8, hLink]
          refine ⟨⟨visited ++ [n], rest, by rw [hSplit]; simp, ?_, ?_⟩, ?_⟩
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hVisited x hx
            · simp only [List.mem_singleton] at hx
              subst hx
              rw [UInt64.le_iff_toNat_le]
              rw [UInt64.lt_iff_toNat_lt] at hLt
              omega
          · simp [previousRoot_append_singleton]
          · simp only [freeHead] at hScanAfter
            omega

theorem freeObject_specA {m : Module} (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (v : ReleaseVars) (hHeap : heap.At store) (hObject : heap.Object store v.object)
    (hRoots : ∀ n ∈ heap.free, n.root.toNat % 8 = 0) (hPtrAl : v.object.toNat % 8 = 0)
    (Q : Assertion Unit) (after : Program)
    (hNext : ∀ previous current, wpA m after Q (heap.releaseStore store v.object)
      (v.atPlace previous current).toLocals env) :
    wpA m (freeObject ++ after) Q store v.toLocals env := by
  obtain ⟨root, count, pending, ptr, kind, length, width, mask, element, slot, child, previous0,
    current0⟩ := v
  simp only [ReleaseVars.atPlace] at hNext hObject
  have hPtrAl' : ptr.toNat % 8 = 0 := hPtrAl
  set capacity := store.mem.read64 (ptr - 32).toUInt32 with hCapacityDef
  have hBase := hObject.base
  have hAddress := hObject.address
  have hBelow := hObject.below
  have hTop := hHeap.top
  have hSeparate := hObject.separate
  simp only [capacityAt] at hAddress hBelow hSeparate
  rw [← hCapacityDef] at hAddress hBelow hSeparate
  have hA (k : UInt64) (hk : k.toNat ≤ 48) :
      (ptr - k).toUInt32 = UInt32.ofNat (ptr.toNat - k.toNat) := by
    rw [Memory.toUInt32_eq_ofNat, LeanExe.Common.toNat_sub_le _ _ (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hA40 := hA 40 (by decide)
  have hA32 := hA 32 (by decide)
  simp only [UInt64.reduceToNat] at hA40 hA32
  have hs40 : (ptr - 40).toNat % 4294967296 = ptr.toNat - 40 := by
    rw [LeanExe.Common.toNat_sub_le _ _ (by simp; omega), Nat.mod_eq_of_lt (by simp; omega)]
    rfl
  have hm40 : (ptr.toNat - 40) % 4294967296 = ptr.toNat - 40 := Nat.mod_eq_of_lt (by omega)
  have hc40 : ¬ store.mem.pages * 65536 < ptr.toNat - 40 + 8 := by omega
  have hpa40 : (ptr.toNat - 40) % 8 = 0 := by omega
  -- The store after the free counter and the write of the count word.
  set mem1 := store.mem.write64 (UInt32.ofNat (ptr.toNat - 40)) 0 with hMem1
  have hw40 : (UInt32.ofNat (ptr.toNat - 40)).toNat = ptr.toNat - 40 := by
    simp only [UInt32.toNat_ofNat', Nat.reducePow, hm40]
  have hw32 : (UInt32.ofNat (ptr.toNat - 32)).toNat = ptr.toNat - 32 := by
    simp only [UInt32.toNat_ofNat', Nat.reducePow]
    exact Nat.mod_eq_of_lt (by omega)
  have hBytes1 : ∀ a, a < ptr.toNat - 48 ∨ ptr.toNat ≤ a → mem1.bytes a = store.mem.bytes a :=
    fun a ha => by
      rw [hMem1, Memory.write64_bytes_outside _ _ _ (by rw [hw40]; omega)]
  have hFree : ∀ n ∈ heap.free, ∀ a, n.root.toNat - 48 ≤ a → a < n.root.toNat →
      a < ptr.toNat - 48 ∨ ptr.toNat ≤ a := fun n hn a hLow hHigh => by
    have := hSeparate n hn
    simp only [regionsDisjoint, FreeNode.region] at this
    omega
  have hList1 : FreeListAt mem1 heap.free :=
    FreeListMemory.frame_headers hHeap.freeList (by simp [hMem1, Wasm.Mem.write64_pages])
      fun n hn a hLow hHigh => hBytes1 a (hFree n hn a hLow hHigh)
  have hCapacity1 : mem1.read64 (ptr - 32).toUInt32 = capacity := by
    rw [hA32, hMem1, Memory.read64_write64_disjoint _ _ _ _ (by rw [hw40, hw32]; omega), ← hA32]
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
  have hGlobals := hHeap.globals
  simp only [freeObject, incrementGlobal, headerStore, releaseObject, List.cons_append,
    List.nil_append, List.append_assoc]
  simp [wpA_simp, wp_simp, ReleaseVars.toLocals, hs40, hm40, hc40, hpa40, hGlobals, Heap.globals]
  refine findPlace_specA env _ heap.free
    ⟨root, count, pending, ptr, kind, length, width, mask, element, slot, child, previous0,
      current0⟩ (by simpa [hMem1] using hList1) (by simp) hRoots _ _ ?_
  simp only [ReleaseVars.atPlace]
  refine joinProgram_specA env _ _ releaseObject releaseCurrent { root := ptr, capacity }
    (aboveNodes ptr heap.free) rfl (by simp [ReleaseVars.toLocals, releaseObject])
    (by simp [ReleaseVars.toLocals, releaseCurrent]) (by simpa [hMem1] using hAbove1) (by simp; omega)
    (by simp; omega) (by simp [Wasm.Mem.write64_pages]; omega)
    (by simpa [hMem1] using hCapacity1) hApartQ hPtrAl' (fun n hn => hRoots n (hAboveMem n hn))
    _ _ ?_
  set mem2 := joinMem mem1 { root := ptr, capacity } (aboveNodes ptr heap.free) with hMem2
  have hBlock : FreeListAt mem2 (joinNodes { root := ptr, capacity } (aboveNodes ptr heap.free)) :=
    FreeListAt.join hAbove1 (by simp; omega) (by simp; omega) (by rw [hPages1]; simp; omega)
      (by
        show mem1.read64 (ptr - 40).toUInt32 = 0
        rw [hA40, hMem1]
        exact Memory.read64_write64 _ _ _)
      hCapacity1 hApartQ
  simp [wpA_simp, wp_simp, ReleaseVars.toLocals, releasePrevious]
  refine wpA_iff_cons rfl ?_
  have hGlobals : (heap.release ptr capacity).globals =
      [.i64 heap.top, .i64 (if belowNodes ptr heap.free = [] then ptr else freeHead heap.free),
        .i64 heap.allocs, .i64 (heap.frees + 1)] := by
    simp [Heap.release, Heap.globals, freeHead_insertFree]
  cases hLast : (belowNodes ptr heap.free).getLast? with
  | none =>
    have hNil : belowNodes ptr heap.free = [] := List.getLast?_eq_none_iff.mp hLast
    have hStore : { store with
        globals := { globals := [.i64 heap.top, .i64 ptr, .i64 heap.allocs,
          .i64 (heap.frees + 1)] }
        mem := mem2 } = heap.releaseStore store ptr := by
      simp only [Heap.releaseStore]
      congr 1
      · rw [hGlobals]
        simp [hNil]
      · simp only [releaseMem, hLast, hMem2, hMem1, hA40, write64_write64_same,
          ← hCapacityDef]
    simp [hNil, previousRoot, wpA_simp, wp_simp]
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
    have hStore : { store with
        globals := { globals := [.i64 heap.top, .i64 (freeHead heap.free), .i64 heap.allocs,
          .i64 (heap.frees + 1)] }
        mem := joinMem mem2 p (joinNodes { root := ptr, capacity } (aboveNodes ptr heap.free)) } =
        heap.releaseStore store ptr := by
      simp only [Heap.releaseStore]
      congr 1
      · rw [hGlobals]
        simp [hNe]
      · simp only [releaseMem, hLast, hMem2, hMem1, hA40, write64_write64_same,
          ← hCapacityDef]
    simp only [hPrevious, hpRoot, ite_false, ne_eq, not_true_eq_false]
    have hpFit2 : p.root.toNat + p.capacity.toNat ≤ mem2.pages * 65536 := by
      rw [hMem2, joinMem_pages, hPages1]
      omega
    rw [← List.append_nil (joinProgram 11 3)]
    refine joinProgram_specA env _ _ releasePrevious releaseObject p
      (joinNodes { root := ptr, capacity } (aboveNodes ptr heap.free)) rfl ?_ ?_ ?_ hp48 hp32
      ?_ ?_ ?_ (hRoots p hp) ?_ _ _ ?_
    · simp [releasePrevious]
    · simp [releaseObject, freeHead_joinNodes]
    · exact hBlock
    · exact hpFit2
    · exact hpCapacity
    · exact joinNodes_apart (block := { root := ptr, capacity }) (by simp; omega)
        (by simp; omega)
        (fun n hn => ⟨(hHeap.freeList.mem_bounds (hAboveMem n hn)).1,
          (hHeap.freeList.mem_bounds (hAboveMem n hn)).2.1⟩)
        (by simp only [FreeNode.region]; omega)
        (by simp only [regionsDisjoint, FreeNode.region]; omega) hpAbove
    · intro n hn
      rcases joinNodes_root hn with h | h
      · rw [h]
        exact hPtrAl'
      · exact hRoots n (hAboveMem n h)
    have h := hNext p.root (freeHead (aboveNodes ptr heap.free))
    rw [← hStore] at h
    simp [wpA_simp, wp_simp]
    exact h

theorem release_leaf_runA {m : Module} {typeIdx : Nat} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx)) (env : HostEnv Unit) (heap : Heap)
    (store : Store Unit) (ptr : UInt64) (hHeap : heap.At store)
    (hObject : heap.Object store ptr)
    (hHeaderMagic : store.mem.read64 (ptr - 48).toUInt32 = objectMagic)
    (hHeaderCount : store.mem.read64 (ptr - 40).toUInt32 = 1)
    (hHeaderMask : store.mem.read64 (ptr - 8).toUInt32 = 0) (hAligned : heap.Aligned)
    (hPtrAl : ptr.toNat % 8 = 0) :
    RunsA false env m 1 store [.i64 ptr] fun final out =>
      out = [] ∧ final = heap.releaseStore store ptr := by
  refine RunsA.of_wpA_entry_for (f := releaseFunction typeIdx)
    (by simpa [hImports] using hFunc) ?_ (by simp [hImports])
  have hBase := hObject.base
  have hBelow := hObject.below
  have hTop := hHeap.top
  have hFit := hObject.address
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
    rw [← hA48]; exact hHeaderMagic
  have hCount : store.mem.read64 (UInt32.ofNat (ptr.toNat - 40)) = 1 := by
    rw [← hA40]; exact hHeaderCount
  have hMask : (store.mem.write64 (UInt32.ofNat (ptr.toNat - 40)) 0).read64
      (UInt32.ofNat (ptr.toNat - 8)) = 0 := by
    rw [← hA40, ← hA8,
      Memory.read64_write64_disjoint _ _ _ _ (by
        rw [headerAddress_toNat (by simp; omega) (by omega),
          headerAddress_toNat (by simp; omega) (by omega)]
        simp only [UInt64.reduceToNat]
        omega)]
    exact hHeaderMask
  have hGlobals := hHeap.globals
  have hb48 : ptr.toNat - 48 + 8 ≤ store.mem.pages * 65536 := by omega
  have hb40 : ptr.toNat - 40 + 8 ≤ store.mem.pages * 65536 := by omega
  have hc40 : ¬ store.mem.pages * 65536 < ptr.toNat - 40 + 8 := by omega
  have hc8 : ¬ store.mem.pages * 65536 < ptr.toNat - 8 + 8 := by omega
  have hpa48 : (ptr.toNat - 48) % 8 = 0 := by omega
  have hpa40 : (ptr.toNat - 40) % 8 = 0 := by omega
  have hpa8 : (ptr.toNat - 8) % 8 = 0 := by omega
  simp [releaseFunction, releaseBody, dropReference, checkMagic, headerLoad, headerStore,
    releaseCount, releasePending, releaseObject, Function.toLocals, Function.numParams,
    ValueType.zero, TrapMsg, wpA_simp, wp_simp, hPtr]
  refine wpA_iff_cons rfl ?_
  simp [wpA_simp, wp_simp, hs48, hm48, hb48, hpa48, hMagic]
  refine wpA_iff_cons rfl ?_
  simp [wpA_simp, wp_simp, hs40, hm40, hb40, hpa40, hCount]
  refine wpA_iff_cons rfl ?_
  simp [wpA_simp, wp_simp, hs40, hm40, hb40, hpa40]
  change wpA m _ _ _ (releaseLocals ptr ptr 0 0 0) env
  refine wpA_block_cons ?_
  refine wpA_loop_cons
    (fun st s => (st = releaseEntry store ptr ∧ s = releaseLocals ptr ptr 0 0 0) ∨
      (st = heap.releaseStore store ptr ∧ ∃ previous current,
        s = releaseLocals ptr 0 ptr previous current))
    (fun _ s => match s.get releasePending with
      | some (.i64 pending) => pending.toNat
      | _ => 0) (Or.inl ⟨rfl, rfl⟩) ?_
  rintro st s (⟨rfl, rfl⟩ | ⟨rfl, previous, current, rfl⟩)
  · simp only [releaseLocals, wpA_simp, wp_simp, releasePending]
    simp only [Locals.get, Locals.set?]
    simp [releaseEntry, hs40, hm40, hc40, hpa40, hPtr]
    simp only [dropChildren, headerLoad, releaseMask, releaseObject, List.cons_append,
      List.nil_append, wpA_simp, wp_simp]
    simp only [Locals.get, Locals.set?]
    simp [hs8, hm8, hc8, hpa8, hMask]
    refine wpA_iff_cons rfl ?_
    simp only [ne_eq, not_true_eq_false, ite_false, wpA_nil]
    obtain ⟨hHeap1, hObject1, hRelease1⟩ := hObject.clearCount hHeap
    change wpA m (freeObject ++ [.br 0]) _ (releaseEntry store ptr)
      (ReleaseVars.toLocals ⟨ptr, 1, 0, ptr, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩) env
    refine freeObject_specA env heap _ _ hHeap1 hObject1 hAligned.roots hPtrAl _ _
      fun previous current => ?_
    dsimp only
    rw [hRelease1]
    simp [wpA_simp, wp_simp, ReleaseVars.atPlace, ReleaseVars.toLocals]
    omega
  · simp [releaseLocals, wpA_simp, wp_simp]

theorem release_null_runA {m : Module} {typeIdx : Nat} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx))
    (env : HostEnv Unit) (store : Store Unit) :
    RunsA false env m 1 store [.i64 0] fun final out => out = [] ∧ final = store := by
  refine RunsA.of_wpA_entry_for (f := releaseFunction typeIdx)
    (by simpa [hImports] using hFunc) ?_ (by simp [hImports])
  simp [releaseFunction, releaseBody, Function.toLocals, Function.numParams, ValueType.zero,
    TrapMsg, wpA_simp, wp_simp]
  refine wpA_iff_cons rfl ?_
  simp [wpA_simp, wp_simp]

end LeanExe.Pipeline
