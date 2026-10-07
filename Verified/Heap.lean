import Verified.State
import LeanExe.Pipeline.RuntimeSpec
import LeanExe.Pipeline.ReleaseTree
import LeanExe.ProofKit.ArrayPrefix

/-! The code that allocates, copies, and releases arrays, and its specifications: a release of an
owned array consumes its block, and a copy of a value puts each of its arrays in a new block. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- A module with the runtime's `alloc` and `release` at functions 0 and 1, no imports, and a
32-bit memory, as `compile` builds it. -/
structure Runtime (m : Module) : Prop where
  imports : m.imports = []
  memory32 : m.memIs64 = false
  alloc : m.funcs[0]? = some (allocFunction 0)
  release : m.funcs[1]? = some (releaseFunction 1)

/-- A release of the owned array at `ptr` is a step that consumes its block. -/
theorem releaseStep {heap : Heap} {store : Store Unit} {ptr : UInt64} {xs : Array UInt64}
    (hAt : heap.At store) (hOwned : heap.Owned store ptr xs) :
    Step heap store (fun r => regionsDisjoint r (block store ptr))
      (heap.release ptr (store.mem.read64 (ptr - 32).toUInt32)) (heap.releaseStore store ptr)
      [] :=
  ⟨hAt.release hOwned.object, rfl, fun r hr hpos hk =>
    Heap.Keeps.release hAt hOwned.object r hr hpos fun b hb => by
      rw [List.mem_singleton.mp hb]; exact hk⟩

/-- A call of `release` on the owned array whose address is on top of the stack. -/
theorem wp_release {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {ptr : UInt64} {xs : Array UInt64} {vs : List Value}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hOwned : heap.Owned store ptr xs)
    (hNext : wp m rest Q (heap.releaseStore store ptr) { s with values := vs } host) :
    wp m (.call 1 :: rest) Q store { s with values := .i64 ptr :: vs } host := by
  have hRun := ((release_run hm.imports hm.release host heap store ptr xs hAt hOwned).runs
    (aborts := false)).append_args (by simp [hm.imports]) (by simpa [hm.imports] using hm.release)
    (by rfl) vs
  refine wp_call_runs hRun trivial fun st' out hPost => ?_
  obtain ⟨out', rfl, rfl, rfl⟩ := hPost
  simpa using hNext

/-- A call of `alloc` on the byte count on top of the stack: the allocation, or a trap at
`unreachable` when memory runs out. -/
theorem wp_alloc {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {bytes : UInt64} {vs : List Value} {rest : Program}
    {Q : Assertion Unit} (hAt : heap.At store) (hBytes : bytes.toNat ≤ 4294967296)
    (hCap : store.memoryCap m 0 ≤ 65535) (hTrap : TrapOK true Q)
    (hNext : heap.Fits (allocSize bytes) →
      wp m rest Q (heap.allocateStore store (allocSize bytes) 1)
        { s with values := .i64 (FixedArrayAllocate.root heap.top (allocSize bytes) heap.free) ::
          vs } host) :
    wp m (.call 0 :: rest) Q store { s with values := .i64 bytes :: vs } host := by
  have hRun := (alloc_spec_or_abort hm.memory32 hm.imports hm.alloc host heap store bytes hAt
    hBytes hCap).append_args (by simp [hm.imports]) (by simpa [hm.imports] using hm.alloc)
    (by rfl) vs
  refine wp_call_runs hRun hTrap fun st' out hPost => ?_
  obtain ⟨out', rfl, hFits, rfl, rfl⟩ := hPost
  simpa using hNext hFits

theorem wrap_toUInt32 (a : UInt64) : UInt32.ofNat (a.toNat % 2 ^ 32) = a.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp [UInt64.toNat_toUInt32]

/-- `wrap_toUInt32` with the modulus as `simp` writes it. -/
theorem ofNat_mod_toUInt32 (a : UInt64) : UInt32.ofNat (a.toNat % 4294967296) = a.toUInt32 :=
  wrap_toUInt32 a

/-- The offset of element `k` of an array of `size` words. -/
theorem element_offset {k : UInt64} {size : Nat} (hk : k.toNat < size)
    (hSize : 8 * (size + 1) ≤ 4294967296) :
    (k + 1) * 8 = UInt64.ofNat (8 * (k.toNat + 1)) := by
  have := hk
  have := hSize
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- The address of element `k` of the array at `ptr`. -/
theorem element_address (ptr : UInt64) (k : Nat) :
    (ptr + (UInt64.ofNat k + 1) * 8).toUInt32 = UInt64Array.wordAddress ptr (k + 1) := by
  unfold UInt64Array.wordAddress
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- The byte count of an array of `size` words is a multiple of 8, which `alloc` keeps. -/
theorem allocSize_words {size : Nat} (h : size < 536870912) :
    ((UInt64.ofNat size + 1) * 8).toNat = 8 * (size + 1) ∧
      allocSize ((UInt64.ofNat size + 1) * 8) = (UInt64.ofNat size + 1) * 8 := by
  have hN : (UInt64.ofNat size).toNat = size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hBytes : ((UInt64.ofNat size + 1) * 8).toNat = 8 * (size + 1) := by
    simp only [UInt64.toNat_mul, UInt64.toNat_add, hN, UInt64.reduceToNat]
    omega
  refine ⟨hBytes, ?_⟩
  have hRound : (((UInt64.ofNat size + 1) * 8 + 7) / 8 * 8).toNat = 8 * (size + 1) := by
    rw [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, hBytes]
    simp only [UInt64.reduceToNat]
    omega
  unfold allocSize
  split
  · rename_i hLt
    rw [UInt64.lt_iff_toNat_lt, hRound] at hLt
    simp at hLt
  · apply UInt64.toNat_inj.mp
    rw [hRound, hBytes]

/-- An array after a write of element `k`: the array with that element replaced. -/
theorem _root_.LeanExe.ProofKit.UInt64Array.At.writeElement {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : UInt64Array.At store ptr values) {k : Nat} (hk : k < values.size) (v : UInt64) :
    UInt64Array.At (UInt64Array.writeElement store ptr k v) ptr (values.set k v hk) := by
  have hFit := h.1
  refine ⟨by simpa using h.1, by simpa using h.2.1, ?_, fun j hj => ?_⟩
  · rw [Array.size_set]
    refine (Memory.read64_write64_disjoint store.mem _ _ ptr.toUInt32 (Or.inl ?_)).trans
      h.lengthRead
    rw [UInt64Array.wordAddress_toNat hFit (by omega), Memory.toUInt32_toNat,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Array.size_set] at hj
    rw [Array.getElem_set]
    show (store.mem.write64 (UInt64Array.wordAddress ptr (k + 1)) v).read64
      (UInt64Array.wordAddress ptr (j + 1)) = _
    split
    · subst k
      exact Memory.read64_write64 ..
    · rw [Memory.read64_write64_disjoint _ _ _ _ (by
        rw [UInt64Array.wordAddress_toNat hFit (by omega),
          UInt64Array.wordAddress_toNat hFit (by omega)]
        omega)]
      exact h.elementRead j hj

/-- The allocation of an array of `n` words, with `n` in local `count`: a new owned block whose
length word is `n` and whose elements are what memory held, with its address in local `ptr`.  The
allocation may trap at `unreachable` when memory runs out. -/
theorem wp_allocArray {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {count ptr : Nat} {n : UInt64} {rest : Program}
    {Q : Assertion Unit} (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK true Q) (hn : n.toNat < 536870912) (hN : s.get count = some (.i64 n))
    (hLow : s.params.length ≤ ptr) (hHigh : ptr < s.params.length + s.locals.length)
    (hne : count ≠ ptr)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (root : UInt64) (words : Array UInt64),
      words.size = n.toNat → Step heap store (fun _ => True) heap' store' [block store' root] →
      heap'.Owned store' root words →
      wp m rest Q store' (setLocal { s with values := s.values } ptr (.i64 root)) host) :
    wp m (allocArrayCode count ptr ++ rest) Q store s host := by
  have hn' : UInt64.ofNat n.toNat = n := UInt64.ofNat_toNat
  obtain ⟨hBytes, hAllocSize⟩ := allocSize_words hn
  rw [hn'] at hBytes hAllocSize
  simp only [allocArrayCode, List.cons_append, List.nil_append, wp_localGet_cons, hN,
    wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons]
  refine wp_alloc hm hAt (by rw [hBytes]; omega) hCap hTrap fun hFits => ?_
  rw [hAllocSize] at hFits ⊢
  generalize hNeed : (n + 1) * 8 = need at hFits hBytes ⊢
  have hBlock := hAt.allocate_block 1 hFits
  have hCapacity := allocated_capacity need heap.free
  generalize hRoot : FixedArrayAllocate.root heap.top need heap.free = root at hBlock ⊢
  generalize hCapDef : allocatedCapacity need heap.free = cap at hBlock hCapacity
  have hRootBase := hBlock.base
  have hRootAddress := hBlock.address
  have hRootMemory := hBlock.memory
  have hRoot32 : root.toUInt32.toNat = root.toNat := by
    rw [Memory.toUInt32_toNat]; omega
  set store1 := heap.allocateStore store need 1 with hStore1
  refine wp_localSet_local (s := s) (vs := s.values) hLow hHigh ?_
  let s1 := setLocal { s with values := s.values } ptr (.i64 root)
  have hLow1 : ({ s with values := s.values } : Locals).params.length ≤ ptr := hLow
  have hRoot1 : s1.get ptr = some (.i64 root) := Locals.get_setLocal_same hLow1 hHigh
  have hN1 : s1.get count = some (.i64 n) := by
    rw [Locals.get_setLocal_ne hLow1 hne]; exact hN
  -- The length word.
  show wp m _ Q store1 s1 host
  simp only [wp_localGet_cons, Locals.get_values, hRoot1, wp_wrapI64_cons, hN1, wp_store64_cons,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega)]
  set store2 : Store Unit :=
    { store1 with mem := (store1.mem.write64 root.toUInt32 n) } with hStore2
  -- The block, owned, with the elements that memory holds.
  let words : Array UInt64 :=
    Array.ofFn (n := n.toNat) fun j => store2.mem.read64 (UInt64Array.wordAddress root (j + 1))
  have hSize : words.size = n.toNat := Array.size_ofFn
  have hValues : UInt64Array.At store2 root words := by
    refine ⟨by rw [hSize]; omega, ?_, ?_, fun i hi => ?_⟩
    · rw [hSize]; simp only [store2, Wasm.Mem.write64_pages]; omega
    · rw [hSize, hn']; exact Memory.read64_write64 ..
    · simp [words, UInt64Array.wordAddress]
  have hWrites : Memory.WritesRange store1 store2 root.toNat (root.toNat + 8) :=
    Memory.WritesRange.write64 _ root.toUInt32 _ _ _ (by omega) (by omega)
  have hWithin : WritesWithin store1 store2 root.toNat cap.toNat :=
    ⟨by rw [hWrites.1], hWrites.2.1, fun a ha => hWrites.2.2 a (by omega)⟩
  subst hRoot hCapDef
  have hNew := Heap.newArray_of_writes hAt hFits hWithin hValues (by rw [hSize]; omega)
    (by rw [hWrites.1]; exact heap.allocateStore_memoryCaps store need 1)
  exact hNext _ store2 _ words hSize
    ⟨hNew.at_, hNew.caps, fun r hr hpos _ => hNew.keeps r hr hpos nofun⟩ hNew.owned

/-- The copy of an array that is readable at `ptr`, whose address local `src` holds, into a new
owned array, with the locals from `base` to `base + 2` as scratch.  The copy allocates, so it may
trap at `unreachable`. -/
theorem wp_copyArray {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {src base : Nat} {ptr : UInt64} {xs : Array UInt64}
    {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hTrap : TrapOK true Q)
    (hB : heap.Borrowed store ptr xs) (hSrc : s.get src = some (.i64 ptr)) (hSrcBase : src < base)
    (hBase : s.params.length ≤ base) (hRoom : base + 3 ≤ s.params.length + s.locals.length)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (ptr' : UInt64),
      Step heap store (fun _ => True) heap' store' [block store' ptr'] →
      heap'.Owned store' ptr' xs → Frame base s s' →
      wp m rest Q store' { s' with values := .i64 ptr' :: s.values } host) :
    wp m (copyArrayCode src base ++ rest) Q store s host := by
  have hA := hB.values
  have hFit := hA.1
  have hLen := hA.lengthBound
  have hSizeLt : xs.size < 536870912 := by omega
  obtain ⟨hBytes, hAllocSize⟩ := allocSize_words hSizeLt
  have hN : (UInt64.ofNat xs.size).toNat = xs.size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  simp only [copyArrayCode, allocArrayCode, List.cons_append, List.nil_append]
  -- The length, in local `base`.
  simp only [wp_localGet_cons, hSrc, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead]
  refine wp_localSet_local hBase (by omega) ?_
  let s1 := setLocal { s with values := s.values } base (.i64 (UInt64.ofNat xs.size))
  have hLow1 : ({ s with values := s.values } : Locals).params.length ≤ base := hBase
  have hN1 : s1.get base = some (.i64 (UInt64.ofNat xs.size)) :=
    Locals.get_setLocal_same hLow1 (by show base < s.params.length + s.locals.length; omega)
  have hSrc1 : s1.get src = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLow1 (by omega)]; exact hSrc
  have hF1 : Frame base s s1 :=
    ⟨rfl, by simp [s1, setLocal], fun j hj => Locals.get_setLocal_ne hLow1 (by omega)⟩
  -- The allocation of the new array.
  show wp m _ Q store s1 host
  simp only [wp_localGet_cons, hN1, wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons]
  refine wp_alloc hm hAt (by rw [hBytes]; omega) hCap hTrap fun hFits => ?_
  rw [hAllocSize] at hFits ⊢
  generalize hNeed : (UInt64.ofNat xs.size + 1) * 8 = need at hFits hBytes ⊢
  have hBlock := hAt.allocate_block 1 hFits
  have hCapacity := allocated_capacity need heap.free
  generalize hRoot : FixedArrayAllocate.root heap.top need heap.free = root at hBlock ⊢
  generalize hCapDef : allocatedCapacity need heap.free = cap at hBlock hCapacity
  have hRootBase := hBlock.base
  have hRootAddress := hBlock.address
  have hRootMemory := hBlock.memory
  have hRoot32 : root.toUInt32.toNat = root.toNat := by
    rw [Memory.toUInt32_toNat]; omega
  set store1 := heap.allocateStore store need 1 with hStore1
  refine wp_localSet_local (s := s1) (vs := s.values) (by show s.params.length ≤ base + 1; omega)
    (by show base + 1 < s1.params.length + s1.locals.length; simp [s1, setLocal]; omega) ?_
  let s2 := setLocal { s1 with values := s.values } (base + 1) (.i64 root)
  have hLow2 : ({ s1 with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s.params.length ≤ base + 1; omega
  have hRoot2 : s2.get (base + 1) = some (.i64 root) :=
    Locals.get_setLocal_same hLow2
      (by show base + 1 < s1.params.length + s1.locals.length; simp [s1, setLocal]; omega)
  have hN2 : s2.get base = some (.i64 (UInt64.ofNat xs.size)) := by
    rw [Locals.get_setLocal_ne hLow2 (by omega)]; exact hN1
  have hSrc2 : s2.get src = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLow2 (by omega)]; exact hSrc1
  -- The length word.
  show wp m _ Q store1 s2 host
  simp only [wp_localGet_cons, Locals.get_values, hRoot2, wp_wrapI64_cons, hN2, wp_store64_cons,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega)]
  set store2 : Store Unit :=
    { store1 with mem := (store1.mem.write64 root.toUInt32 (UInt64.ofNat xs.size)) } with hStore2
  -- The index, in local `base + 2`.
  simp only [wp_constI64_cons]
  refine wp_localSet_local (s := s2) (vs := s.values)
    (by show s.params.length ≤ base + 2; omega)
    (by show base + 2 < s2.params.length + s2.locals.length; simp [s2, s1, setLocal]; omega) ?_
  let s3 := setLocal { s2 with values := s.values } (base + 2) (.i64 0)
  have hLow3 : ({ s2 with values := s.values } : Locals).params.length ≤ base + 2 := by
    show s.params.length ≤ base + 2; omega
  have hParams3 : s3.params = s.params := rfl
  have hLength3 : s3.locals.length = s.locals.length := by simp [s3, s2, s1, setLocal]
  have hF3 : Frame base s s3 := by
    refine ⟨rfl, hLength3, fun j hj => ?_⟩
    rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values,
      Locals.get_setLocal_ne hLow2 (by omega), Locals.get_values]
    exact hF1.below j hj
  have hIdx3 : s3.get (base + 2) = some (.i64 0) :=
    Locals.get_setLocal_same hLow3
      (by show base + 2 < s2.params.length + s2.locals.length; simp [s2, s1, setLocal]; omega)
  have hN3 : s3.get base = some (.i64 (UInt64.ofNat xs.size)) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega)]; exact hN2
  have hRoot3 : s3.get (base + 1) = some (.i64 root) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega)]; exact hRoot2
  have hSrc3 : s3.get src = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega)]; exact hSrc2
  -- The source array stays readable while the code writes inside the new block.
  obtain ⟨hRegionA, hBytesA, hApartA⟩ := hB.region.allocate 1 hAt hFits
  have hTopA : (heap.allocate need).top.toNat ≤ store1.mem.pages * 65536 :=
    (hAt.allocate 1 hFits).top
  have hBelowA : ptr.toNat + 8 * (xs.size + 1) ≤ (heap.allocate need).top.toNat :=
    hRegionA.below
  have hSrcAt : ∀ st : Store Unit,
      Memory.WritesRange store1 st root.toNat (root.toNat + 8 * (xs.size + 1)) →
      UInt64Array.At st ptr xs := by
    intro st hW
    rw [hRoot, hCapDef] at hApartA
    simp only [regionsDisjoint] at hApartA
    refine arrayAt_frameIn hA ?_ fun a hl hh => ?_
    · rw [hW.2.1]; omega
    · rw [hW.2.2 a (by omega)]
      exact hBytesA a hl hh
  have hPrefix2 : UInt64Array.PrefixAt store2 root xs 0 := by
    refine UInt64Array.PrefixAt.empty _ _ _ (by omega) ?_ ?_
    · simp only [store2, Wasm.Mem.write64_pages]; omega
    · exact Memory.read64_write64 ..
  have hWrites2 : Memory.WritesRange store1 store2 root.toNat (root.toNat + 8 * (xs.size + 1)) :=
    Memory.WritesRange.write64 _ root.toUInt32 _ _ _ (by omega) (by omega)
  -- The loop: element `k` of the source goes to element `k` of the new array.
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st si => ∃ k, k ≤ xs.size ∧ UInt64Array.PrefixAt st root xs k ∧
      Memory.WritesRange store1 st root.toNat (root.toNat + 8 * (xs.size + 1)) ∧
      Frame base s si ∧ si.get base = some (.i64 (UInt64.ofNat xs.size)) ∧
      si.get (base + 1) = some (.i64 root) ∧ si.get (base + 2) = some (.i64 (UInt64.ofNat k)) ∧
      si.get src = some (.i64 ptr))
    (fun _ si => match si.get (base + 2) with
      | some (.i64 i) => xs.size - i.toNat
      | _ => 0)
    ⟨0, Nat.zero_le _, hPrefix2, hWrites2, hF3, hN3, hRoot3, hIdx3, hSrc3⟩ ?_
  rintro st si ⟨k, hk, hPrefix, hWrites, hFi, hNi, hRooti, hIdxi, hSrci⟩
  have hk64 : (UInt64.ofNat k).toNat = k :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  simp only [wp_localGet_cons, Locals.get_values, hIdxi, hNi, wp_geUI64_cons, wp_br_if_cons]
  by_cases hDone : UInt64.ofNat xs.size ≤ UInt64.ofNat k
  · -- The copy is complete.
    have hkEq : k = xs.size := by
      rw [UInt64.le_iff_toNat_le, hk64, hN] at hDone; omega
    subst hkEq
    simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    simp only [hRooti]
    have hValues := hPrefix.complete
    have hWithin : WritesWithin store1 st root.toNat cap.toNat :=
      ⟨by rw [hWrites.1], hWrites.2.1, fun a ha => hWrites.2.2 a (by omega)⟩
    subst hRoot hCapDef
    have hNew := Heap.newArray_of_writes hAt hFits hWithin hValues (by omega)
      (by rw [hWrites.1]; exact heap.allocateStore_memoryCaps store need 1)
    exact hNext _ st si _ ⟨hNew.at_, hNew.caps, fun r hr hpos _ => hNew.keeps r hr hpos nofun⟩
      hNew.owned hFi
  · -- One more element.
    have hLess : k < xs.size := by
      rw [UInt64.le_iff_toNat_le, hk64, hN] at hDone; omega
    simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte]
    have hSrcAt' := hSrcAt st hWrites
    have hElement := hPrefix.elementBound k hLess
    have hSrcElement := hSrcAt'.elementBound k hLess
    simp only [wp_localGet_cons, Locals.get_values, hRooti, hIdxi, hSrci, wp_constI64_cons,
      wp_addI64_cons, wp_mulI64_cons, wp_wrapI64_cons, wp_load64_cons, wp_store64_cons,
      wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero, element_address]
    have hRead : st.mem.read64 (UInt64Array.wordAddress ptr (k + 1)) = xs[k] :=
      hSrcAt'.elementRead k hLess
    rw [ite_eq_right (by rw [UInt64Array.wordAddress]; omega), hRead,
      ite_eq_right (by omega)]
    have hFitRoot : root.toNat + 8 * (xs.size + 1) ≤ 4294967296 := by omega
    have hLowI : si.params.length ≤ base + 2 := by rw [hFi.params]; omega
    have hHighI : base + 2 < si.params.length + si.locals.length := by
      rw [hFi.params, hFi.length]; omega
    refine wp_localSet_local (s := si) (vs := si.values) hLowI hHighI ?_
    rw [wp_br_cons]
    dsimp only
    have hLowI' : ({ si with values := si.values } : Locals).params.length ≤ base + 2 := hLowI
    have hSucc : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
      rw [UInt64.ofNat_add]; rfl
    have hSucc64 : (UInt64.ofNat (k + 1)).toNat = k + 1 :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    refine ⟨⟨k + 1, hLess, hPrefix.write_next hLess,
      hWrites.trans (UInt64Array.writeElement_frame st root xs.size k xs[k] hFitRoot hLess),
      ⟨hFi.params, by simp [setLocal, hFi.length], fun j hj => ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [Locals.get_values, Locals.get_setLocal_ne hLowI' (by omega), Locals.get_values]
      exact hFi.below j hj
    · rw [Locals.get_setLocal_ne hLowI' (by omega), Locals.get_values]; exact hNi
    · rw [Locals.get_setLocal_ne hLowI' (by omega), Locals.get_values]; exact hRooti
    · rw [Locals.get_setLocal_same hLowI' hHighI, hSucc]
    · rw [Locals.get_setLocal_ne hLowI' (by omega), Locals.get_values]; exact hSrci
    · simp only [Locals.get_setLocal_same hLowI' hHighI, hSucc,
        hSucc64, hk64]
      omega

/-- The copy of a value of type `t` whose words locals `src` on hold and that its words represent
in `heap` at `store`: each of its arrays goes to a new owned block, and the other words stay as
they are.  The copy consumes nothing. -/
theorem wp_copyCode {m : Module} (hm : Runtime m) {host : HostEnv Unit} :
    (t : Ty) → ∀ {heap : Heap} {store : Store Unit} {s : Locals} {src base : Nat} {mode : Mode}
      {ws : List Value} {v : t.denote} {rest : Program} {Q : Assertion Unit},
    heap.At store → store.memoryCap m 0 ≤ 65535 → TrapOK true Q →
    t.Rep mode heap store ws v → LocalsHold s src ws → src + t.width ≤ base →
    s.params.length ≤ base → base + t.copyScratch ≤ s.params.length + s.locals.length →
    (∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (ws' : List Value),
      Step heap store (fun _ => True) heap' store' (t.blocks store' ws' v) →
      t.Rep .owned heap' store' ws' v → Frame base s s' →
      wp m rest Q store' { s' with values := ws'.reverse ++ s.values } host) →
    wp m (copyCode t src base ++ rest) Q store s host
  | .word, heap, store, s, src, base, mode, ws, v, rest, Q, hAt, _, _, hRep, hold, _, _, _,
      hNext => by
    simp only [Ty.rep_word] at hRep
    subst hRep
    have h0 : s.get src = some (.i64 v) := by simpa using hold 0 (by simp)
    simp only [copyCode, List.cons_append, List.nil_append, wp_localGet_cons, h0]
    simpa using hNext heap store s [.i64 v] (Step.refl hAt _) rfl (Frame.refl base s)
  | .bool, heap, store, s, src, base, mode, ws, v, rest, Q, hAt, _, _, hRep, hold, _, _, _,
      hNext => by
    simp only [Ty.rep_bool] at hRep
    subst hRep
    have h0 : s.get src = some (.i64 (boolWord v)) := by simpa using hold 0 (by simp)
    simp only [copyCode, List.cons_append, List.nil_append, wp_localGet_cons, h0]
    simpa using hNext heap store s [.i64 (boolWord v)] (Step.refl hAt _) rfl (Frame.refl base s)
  | .array, heap, store, s, src, base, mode, ws, v, rest, Q, hAt, hCap, hTrap, hRep, hold, hSrc,
      hBase, hRoom, hNext => by
    obtain ⟨ptr, rfl, ha⟩ := hRep
    have h0 : s.get src = some (.i64 ptr) := by simpa using hold 0 (by simp)
    simp only [copyCode]
    exact wp_copyArray hm hAt hCap hTrap ha.borrow h0 (by simp [Ty.width] at hSrc; omega) hBase
      (by simpa [Ty.copyScratch, Ty.scalar] using hRoom) fun heap' store' s' ptr' hStep hOwned hF =>
        hNext heap' store' s' [.i64 ptr'] hStep ⟨ptr', rfl, hOwned⟩ hF
  | .pair a b, heap, store, s, src, base, mode, ws, v, rest, Q, hAt, hCap, hTrap, hRep, hold,
      hSrc, hBase, hRoom, hNext => by
    obtain ⟨first, second, rfl, h1, h2, -⟩ := hRep
    have hl1 := h1.length
    obtain ⟨hold1, hold2⟩ := LocalsHold.append.mp hold
    rw [hl1] at hold2
    simp only [copyCode, List.append_assoc]
    have hScratch : ∀ c : Ty, (c = a ∨ c = b) → c.copyScratch ≤ (Ty.pair a b).copyScratch := by
      intro c hc
      unfold Ty.copyScratch
      by_cases hp : (Ty.pair a b).scalar = true
      · have := Ty.scalar_pair hp
        rcases hc with rfl | rfl <;> simp_all
      · rw [ite_eq_right hp]; split <;> omega
    refine wp_copyCode hm a hAt hCap hTrap h1 hold1 (by simp [Ty.width] at hSrc; omega) hBase
      (by have := hScratch a (Or.inl rfl); omega) fun heap1 store1 s1 ws1 hStep1 hRep1 hF1 => ?_
    have hR2 := (h2.step hStep1 fun _ _ => trivial).1
    refine wp_copyCode hm b hStep1.at_ (by rw [hStep1.cap m]; exact hCap) hTrap hR2
      (s := { s1 with values := ws1.reverse ++ s.values })
      (fun k hk => by
        show s1.get (src + a.width + k) = _
        have := h2.length
        rw [hF1.below _ (by simp [Ty.width] at hSrc; omega)]
        exact hold2 k hk)
      (by simp [Ty.width] at hSrc; omega)
      (by show s1.params.length ≤ base; rw [hF1.params]; exact hBase)
      (by show base + b.copyScratch ≤ s1.params.length + s1.locals.length
          rw [hF1.params, hF1.length]; have := hScratch b (Or.inr rfl); omega)
      fun heap2 store2 s2 ws2 hStep2 hRep2 hF2 => ?_
    obtain ⟨hRep1', hSame1, hFresh1⟩ := hRep1.step hStep2 fun _ _ => trivial
    have hBlocks1 : a.blocks store2 ws1 v.1 = a.blocks store1 ws1 v.1 := hSame1
    have hStep := hStep1.transBoth (keep := fun _ => True) hStep2
      fun _ _ => ⟨trivial, fun _ => trivial⟩
    refine hNext heap2 store2 s2 (ws1 ++ ws2) ?_
      ⟨ws1, ws2, rfl, hRep1', hRep2, fun _ x hx y hy => ?_⟩
      (hF1.trans hF2.values) |> fun h => by simpa [List.reverse_append, List.append_assoc] using h
    · rw [Ty.blocks_append hRep1.length, hBlocks1]
      exact hStep
    · rw [hBlocks1] at hx
      exact hFresh1 x hx y hy

/-- The release of the owned value of type `t` whose words locals `src` on hold: a step that
consumes the value's blocks. -/
theorem wp_releaseCode {m : Module} (hm : Runtime m) {host : HostEnv Unit} :
    (t : Ty) → ∀ {heap : Heap} {store : Store Unit} {s : Locals} {src : Nat} {ws : List Value}
      {v : t.denote} {rest : Program} {Q : Assertion Unit},
    heap.At store → t.Rep .owned heap store ws v → LocalsHold s src ws →
    (∀ (heap' : Heap) (store' : Store Unit),
      Step heap store (fun r => ∀ b ∈ t.blocks store ws v, regionsDisjoint r b) heap' store' [] →
      wp m rest Q store' s host) →
    wp m (releaseCode t src ++ rest) Q store s host
  | .word, heap, store, _, _, _, _, _, _, hAt, _, _, hNext => by
    simpa [releaseCode] using hNext heap store (Step.refl hAt _)
  | .bool, heap, store, _, _, _, _, _, _, hAt, _, _, hNext => by
    simpa [releaseCode] using hNext heap store (Step.refl hAt _)
  | .array, heap, store, s, src, ws, v, rest, Q, hAt, hRep, hold, hNext => by
    obtain ⟨ptr, rfl, hOwned⟩ := hRep
    have h0 : s.get src = some (.i64 ptr) := by simpa using hold 0 (by simp)
    simp only [releaseCode, List.cons_append, List.nil_append, wp_localGet_cons, h0]
    refine wp_release hm hAt hOwned ?_
    have := hNext _ _ ((releaseStep hAt hOwned).mono (fun r hr => hr _ (List.mem_singleton_self _))
      (fun _ h => h))
    simpa using this
  | .pair a b, heap, store, s, src, ws, v, rest, Q, hAt, hRep, hold, hNext => by
    obtain ⟨first, second, rfl, h1, h2, hd⟩ := hRep
    have hl1 := h1.length
    obtain ⟨hold1, hold2⟩ := LocalsHold.append.mp hold
    rw [hl1] at hold2
    simp only [releaseCode, List.append_assoc]
    refine wp_releaseCode hm a hAt h1 hold1 fun heap1 store1 hStep1 => ?_
    -- The second component's blocks lie apart from the first's, so the first release keeps them.
    obtain ⟨hR2, hSame2, -⟩ :=
      h2.step hStep1 fun r hr x hx => regionsDisjoint_symm (hd rfl x hx r hr)
    have hBlocks2 : b.blocks store1 second v.2 = b.blocks store second v.2 := hSame2
    refine wp_releaseCode hm b hStep1.at_ hR2 hold2 fun heap2 store2 hStep2 => ?_
    refine hNext heap2 store2 (hStep1.trans hStep2 fun r hr => ⟨fun x hx => ?_, fun _ x hx => ?_⟩)
    · rw [Ty.blocks_append hl1] at hr
      exact hr x (List.mem_append_left _ hx)
    · rw [Ty.blocks_append hl1] at hr
      rw [hBlocks2] at hx
      exact hr x (List.mem_append_right _ hx)

/-- The state evolved from `heap` at `store` with locals `s` to `heap'` at `store'` with `s'`:
a step that consumes the blocks of the owned variables that die between `liveIn` and `live`, no
change below `base`, and the variables live in `live` still holding their values. -/
structure Evolves {Γ : List Ty} (env : Env Γ) (slots : List Slot) (liveIn live : Nat → Bool)
    (base : Nat) (heap : Heap) (store : Store Unit) (s : Locals) (heap' : Heap)
    (store' : Store Unit) (s' : Locals) : Prop where
  step : Step heap store (Holds.KeepDying env slots liveIn live store s) heap' store' []
  frame : Frame base s s'
  holds : Holds env slots live base heap' store' s'

namespace Evolves

variable {Γ : List Ty} {env : Env Γ} {slots : List Slot} {base : Nat}

/-- No change, when no owned variable dies. -/
theorem refl {heap : Heap} {store : Store Unit} {s : Locals} {liveIn live : Nat → Bool}
    (hAt : heap.At store) (h : Holds env slots liveIn base heap store s)
    (hLive : ∀ i < Γ.length, live i = true → liveIn i = true) :
    Evolves env slots liveIn live base heap store s heap store s :=
  ⟨⟨hAt, rfl, fun _ hr _ _ => ⟨fun _ _ _ => rfl, hr, nofun⟩⟩, Frame.refl base s,
    h.live_mono' hLive⟩

theorem trans {L0 L1 L2 : Nat → Bool} {heap heap1 heap2 : Heap}
    {store store1 store2 : Store Unit} {s s1 s2 : Locals}
    (h0 : Holds env slots L0 base heap store s)
    (e1 : Evolves env slots L0 L1 base heap store s heap1 store1 s1)
    (e2 : Evolves env slots L1 L2 base heap1 store1 s1 heap2 store2 s2)
    (h21 : ∀ i, L2 i = true → L1 i = true) (h10 : ∀ i, L1 i = true → L0 i = true) :
    Evolves env slots L0 L2 base heap store s heap2 store2 s2 :=
  ⟨e1.step.trans e2.step fun r hr =>
      ⟨hr.mono fun i h1 h2 => ⟨h1, by
          cases h : L2 i with
          | false => rfl
          | true => rw [h21 i h] at h2; exact nomatch h2⟩,
        fun _ => Holds.KeepDying.transfer h0 e1.step (fun j hj => e1.frame.below j hj) h10
          (fun i h1 _ => h1) (hr.mono fun i h1 h2 => ⟨h10 _ h1, h2⟩)⟩,
    e1.frame.trans e2.frame, e2.holds⟩

/-- An evolution to fewer live variables. -/
theorem mono {liveIn live live' : Nat → Bool} {heap heap' : Heap} {store store' : Store Unit}
    {s s' : Locals} (e : Evolves env slots liveIn live base heap store s heap' store' s')
    (h : ∀ i, live' i = true → live i = true) :
    Evolves env slots liveIn live' base heap store s heap' store' s' :=
  ⟨e.step.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨h1, by
      cases hl : live' i with
      | false => rfl
      | true => rw [h i hl] at h2; exact nomatch h2⟩) fun _ hb => hb,
    e.frame, e.holds.live_mono h⟩

end Evolves

/-- The release of the owned variables at the indices `is`, each once: the state evolves to one
in which they are no longer live. -/
theorem wp_releaseVars {m : Module} (hm : Runtime m) {host : HostEnv Unit} {Γ : List Ty}
    {env : Env Γ} {slots : List Slot} {base : Nat} :
    (is : List Nat) → is.Nodup → ∀ {live : Nat → Bool} {heap : Heap} {store : Store Unit}
      {s : Locals} {rest : Program} {Q : Assertion Unit},
    Holds env slots live base heap store s → heap.At store → (∀ i ∈ is, live i = true) →
    (∀ heap' store', Evolves env slots live (fun i => live i && !is.contains i) base heap store
      s heap' store' s → wp m rest Q store' s host) →
    wp m (is.flatMap (releaseVar Γ slots) ++ rest) Q store s host
  | [], _, live, heap, store, s, rest, Q, hVars, hAt, _, hNext => by
    simpa using hNext heap store (Evolves.refl hAt hVars fun i _ h => by simpa using h)
  | i :: is, hNodup, live, heap, store, s, rest, Q, hVars, hAt, hLive, hNext => by
    have hi : i ∉ is := (List.nodup_cons.mp hNodup).1
    have hNodup' := (List.nodup_cons.mp hNodup).2
    let live1 := fun j => live j && j != i
    have hSub1 : ∀ j, live1 j = true → live j = true := fun j h => by
      simp only [live1, Bool.and_eq_true] at h; exact h.1
    -- The rest of the list, from the state after variable `i`.
    have hRest : ∀ heap1 store1, Evolves env slots live live1 base heap store s heap1 store1 s →
        wp m (is.flatMap (releaseVar Γ slots) ++ rest) Q store1 s host := by
      intro heap1 store1 e1
      refine wp_releaseVars hm is hNodup' e1.holds e1.step.at_ (fun j hj => ?_)
        fun heap2 store2 e2 => ?_
      · simp only [live1, Bool.and_eq_true, bne_iff_ne]
        exact ⟨hLive j (List.mem_cons_of_mem _ hj), fun he => hi (he ▸ hj)⟩
      · have e := Evolves.trans hVars e1 e2 (fun j h => by
          simp only [Bool.and_eq_true] at h; exact h.1) hSub1
        have hEq : (fun j => live1 j && !is.contains j) =
            (fun j => live j && !(i :: is).contains j) := by
          funext j
          simp only [live1, List.contains_cons]
          cases live j <;> cases hj : (j == i) <;> simp_all [bne, beq_iff_eq]
        rw [hEq] at e
        exact hNext heap2 store2 e
    simp only [List.flatMap_cons, List.append_assoc, releaseVar]
    cases hTy : Γ[i]? with
    | none =>
      simp only
      exact hRest heap store (Evolves.refl hAt hVars fun j _ h => hSub1 j h)
    | some t =>
      simp only
      let x := Var.ofIndex Γ i hTy
      have hxi : x.index = i := Var.index_ofIndex Γ i hTy
      obtain ⟨hBelow, ws, hold, hRep⟩ := hVars.get x (by rw [hxi]; exact hLive i (by simp))
      rw [hxi] at hold hRep
      by_cases hOwned : (slots.getD i default).mode = .owned
      · simp only [hOwned, ↓reduceIte]
        rw [hOwned] at hRep
        refine wp_releaseCode hm t hAt hRep hold fun heap1 store1 hStep1 => hRest heap1 store1 ?_
        refine ⟨hStep1.mono (fun r hr b hb => hr t x (by rw [hxi]; exact hLive i (by simp))
            (by simp [live1, hxi]) (by rw [hxi]; exact hOwned) ws (by rw [hxi]; exact hold)
            (by rw [hRep.length]) b hb) (fun _ h => h), Frame.refl base s, ?_⟩
        refine (hVars.live_mono hSub1).step hStep1 fun u y hy wy hwy hly c hc b hb => ?_
        have hne : x.index ≠ y.index := by
          rw [hxi]; intro he
          simp only [live1, Bool.and_eq_true, bne_iff_ne] at hy
          exact hy.2 he.symm
        exact regionsDisjoint_symm (hVars.2 t u x y (by rw [hxi]; exact hLive i (by simp))
          (hSub1 _ hy) hne (by rw [hxi]; exact hOwned) ws wy (by rw [hxi]; exact hold)
          hRep.length hwy hly b hb c hc)
      · simp only [hOwned, ↓reduceIte, List.nil_append]
        exact hRest heap store (Evolves.refl hAt hVars fun j _ h => hSub1 j h)

/-- The release of the owned variables that `sel` selects among those live. -/
theorem wp_releaseWhere {m : Module} (hm : Runtime m) {host : HostEnv Unit} {Γ : List Ty}
    {env : Env Γ} {slots : List Slot} {base : Nat} {sel live : Nat → Bool} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit}
    (hVars : Holds env slots live base heap store s) (hAt : heap.At store)
    (hSel : ∀ i, sel i = true → live i = true)
    (hNext : ∀ heap' store', Evolves env slots live (fun i => live i && !sel i) base heap store
      s heap' store' s → wp m rest Q store' s host) :
    wp m (releaseWhere Γ slots sel ++ rest) Q store s host := by
  unfold releaseWhere
  refine wp_releaseVars hm _ (List.nodup_range.filter _) hVars hAt
    (fun i hi => hSel i (List.mem_filter.mp hi).2) fun heap' store' e => hNext heap' store' ?_
  have hSame : ∀ i < Γ.length,
      (((List.range Γ.length).filter sel).contains i) = sel i := by
    intro i hi
    cases h : sel i <;> simp [List.mem_filter, hi, h]
  exact ⟨e.step.mono (fun r hr => hr.congr fun i hi h1 h2 => ⟨h1, by rw [← hSame i hi]; exact h2⟩)
      (fun _ h => h), e.frame,
    e.holds.live_mono' fun i hi h => by rw [hSame i hi]; exact h⟩

end Verified
