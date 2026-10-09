import Verified.State
import Verified.Bound
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

/-- Whether `top` can rise by `n` bytes within the memory cap of `m`. -/
def _root_.LeanExe.Pipeline.Heap.Within (heap : Heap) (store : Store Unit) (m : Module) (n : Nat) : Prop :=
  heap.top.toNat + n ≤ 65536 * store.memoryCap m 0

instance {heap : Heap} {store : Store Unit} {m : Module} {n : Nat} :
    Decidable (heap.Within store m n) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem _root_.LeanExe.Pipeline.Heap.Within.mono {heap : Heap} {store : Store Unit} {m : Module} {n n' : Nat}
    (h : heap.Within store m n) (hle : n' ≤ n) : heap.Within store m n' := by
  unfold Heap.Within at *; omega

/-- An allocation of `need` bytes for which `top` can rise by `48 + need` within the cap has the
room that `alloc` needs. -/
theorem _root_.LeanExe.Pipeline.Heap.Within.room {heap : Heap} {store : Store Unit} {m : Module} {need : UInt64}
    (h : heap.Within store m (48 + need.toNat)) (hCap : store.memoryCap m 0 ≤ 65535) :
    heap.Room store m need := by
  unfold Heap.Within at h
  intro _
  unfold FixedArrayBump.requiredPages
  constructor
  · omega
  · intro _; omega

/-- An allocation that fits raises `top` by at most `48 + need`. -/
theorem _root_.LeanExe.Pipeline.Heap.allocate_top {heap : Heap} {need : UInt64} (h : heap.Fits need) :
    (heap.allocate need).top.toNat ≤ heap.top.toNat + allocCost need.toNat := by
  have hTop := allocatedTop_toNat heap.top need heap.free h.fit32
  simp only [Heap.allocate, allocCost]
  rw [hTop]
  split <;> omega

/-- A call of `alloc` on the byte count on top of the stack: the allocation, which raises `top`
by at most `c`, or a trap at `unreachable`, which happens only when `top` cannot rise by `c`
within the cap. -/
theorem wp_alloc {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {bytes : UInt64} {vs : List Value} {rest : Program}
    {Q : Assertion Unit} {c : Nat} (hAt : heap.At store) (hBytes : bytes.toNat ≤ 4294967296)
    (hCap : store.memoryCap m 0 ≤ 65535) (hc : allocCost (allocSize bytes).toNat ≤ c)
    (hTrap : TrapOK (!decide (heap.Within store m c)) Q)
    (hNext : heap.Fits (allocSize bytes) →
      (heap.allocate (allocSize bytes)).top.toNat ≤ heap.top.toNat + c →
      wp m rest Q (heap.allocateStore store (allocSize bytes) 1)
        { s with values := .i64 (FixedArrayAllocate.root heap.top (allocSize bytes) heap.free) ::
          vs } host) :
    wp m (.call 0 :: rest) Q store { s with values := .i64 bytes :: vs } host := by
  have hRun := (alloc_spec_runs (!decide (heap.Within store m c)) hm.memory32 hm.imports hm.alloc
    host heap store bytes hAt hBytes hCap fun hw => by
      simp only [Bool.not_eq_false'] at hw
      exact ((of_decide_eq_true hw).mono hc).room hCap).append_args (by simp [hm.imports])
    (by simpa [hm.imports] using hm.alloc) (by rfl) vs
  refine wp_call_runs hRun hTrap fun st' out hPost => ?_
  obtain ⟨out', rfl, hFits, rfl, rfl⟩ := hPost
  simpa using hNext hFits ((Heap.allocate_top hFits).trans (by omega))

theorem wrap_toUInt32 (a : UInt64) : UInt32.ofNat (a.toNat % 2 ^ 32) = a.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp [UInt64.toNat_toUInt32]

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
    {values : Array UInt64} (h : UInt64Array.At store ptr values) {k : Nat}
    (hk : k < values.size) (v : UInt64) :
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

/-- The allocation of a block of `bytes` bytes, the count on top of the stack, for an array of
`n` words, with `n` in local `len`: a new owned block of at least `bytes` bytes whose length word
is `n` and whose elements are what memory held, with its address in local `ptr`.  The allocation
may trap at `unreachable` when memory runs out. -/
theorem wp_allocBlock {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {len ptr : Nat} {n bytes : UInt64} {vs : List Value}
    {rest : Program} {Q : Assertion Unit} {c : Nat} (hAt : heap.At store)
    (hCap : store.memoryCap m 0 ≤ 65535) (hc : allocCost (allocSize bytes).toNat ≤ c)
    (hTrap : TrapOK (!decide (heap.Within store m c)) Q) (hn : n.toNat < 536870912)
    (hBytes : 8 * (n.toNat + 1) ≤ bytes.toNat) (hBytes32 : bytes.toNat ≤ 4294967296)
    (hN : s.get len = some (.i64 n)) (hLow : s.params.length ≤ ptr)
    (hHigh : ptr < s.params.length + s.locals.length) (hne : len ≠ ptr)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (root : UInt64) (words : Array UInt64),
      words.size = n.toNat → Step heap store (fun _ => True) heap' store' [block store' root] →
      heap'.Owned store' root words → bytes.toNat ≤ capacityAt store' root →
      heap'.top.toNat ≤ heap.top.toNat + c →
      wp m rest Q store' (setLocal { s with values := vs } ptr (.i64 root)) host) :
    wp m (allocBlockCode len ptr ++ rest) Q store { s with values := .i64 bytes :: vs } host := by
  have hn' : UInt64.ofNat n.toNat = n := UInt64.ofNat_toNat
  simp only [allocBlockCode, List.cons_append, List.nil_append]
  refine wp_alloc hm hAt hBytes32 hCap hc hTrap fun hFits hTop => ?_
  have hRound := le_allocSize hBytes32
  generalize hNeed : allocSize bytes = need at hFits hRound hTop ⊢
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
  refine wp_localSet_local (s := s) (vs := vs) hLow hHigh ?_
  let s1 := setLocal { s with values := vs } ptr (.i64 root)
  have hLow1 : ({ s with values := vs } : Locals).params.length ≤ ptr := hLow
  have hRoot1 : s1.get ptr = some (.i64 root) := Locals.get_setLocal_same hLow1 hHigh
  have hN1 : s1.get len = some (.i64 n) := by
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
  have hCapEq := ((hAt.allocate_block 1 hFits).writesWithin hWithin).capacity_eq
  have hNew := Heap.newArray_of_writes hAt hFits hWithin hValues (by rw [hSize]; omega)
    (by rw [hWrites.1]; exact heap.allocateStore_memoryCaps store need 1)
  exact hNext _ store2 _ words hSize
    ⟨hNew.at_, hNew.caps, fun r hr hpos _ => hNew.keeps r hr hpos nofun⟩ hNew.owned
    (by rw [hCapEq]; omega) hTop

/-- The allocation of an array of `n` words, with `n` in local `count`: a new owned block whose
length word is `n` and whose elements are what memory held, with its address in local `ptr`.  The
allocation may trap at `unreachable` when memory runs out. -/
theorem wp_allocArray {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {count ptr : Nat} {n : UInt64} {rest : Program}
    {Q : Assertion Unit} {c : Nat} (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hc : allocCost (8 * (n.toNat + 1)) ≤ c) (hTrap : TrapOK (!decide (heap.Within store m c)) Q)
    (hn : n.toNat < 536870912) (hN : s.get count = some (.i64 n))
    (hLow : s.params.length ≤ ptr) (hHigh : ptr < s.params.length + s.locals.length)
    (hne : count ≠ ptr)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (root : UInt64) (words : Array UInt64),
      words.size = n.toNat → Step heap store (fun _ => True) heap' store' [block store' root] →
      heap'.Owned store' root words → heap'.top.toNat ≤ heap.top.toNat + c →
      wp m rest Q store' (setLocal { s with values := s.values } ptr (.i64 root)) host) :
    wp m (allocArrayCode count ptr ++ rest) Q store s host := by
  have hn' : UInt64.ofNat n.toNat = n := UInt64.ofNat_toNat
  obtain ⟨hBytes, hSize⟩ := allocSize_words hn
  rw [hn'] at hBytes hSize
  simp only [allocArrayCode, List.cons_append, List.nil_append, wp_localGet_cons, hN,
    wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons]
  exact wp_allocBlock hm hAt hCap (by rw [hSize, hBytes]; exact hc) hTrap hn (by rw [hBytes])
    (by rw [hBytes]; omega) hN hLow hHigh hne fun heap' store' root words hSize hStep hOwned _ hTop =>
      hNext heap' store' root words hSize hStep hOwned hTop

/-- `words` with elements `k` to `k + i - 1` replaced by the first `i` elements of `xs`. -/
def overlay (words xs : Array UInt64) (k i : Nat) : Array UInt64 :=
  Array.ofFn (n := words.size) fun j =>
    if k ≤ j.val ∧ j.val < k + i then xs[j.val - k]! else words[j.val]

theorem overlay_size (words xs : Array UInt64) (k i : Nat) :
    (overlay words xs k i).size = words.size := Array.size_ofFn

theorem overlay_zero (words xs : Array UInt64) (k : Nat) : overlay words xs k 0 = words := by
  apply Array.ext (overlay_size ..) fun j _ _ => ?_
  simp only [overlay, Array.getElem_ofFn]
  rw [ite_eq_right (by omega)]

theorem overlay_succ {words xs : Array UInt64} {k i : Nat} (hki : k + i < words.size)
    (hi : i < xs.size) :
    (overlay words xs k i).set (k + i) xs[i] (by rw [overlay_size]; exact hki) =
      overlay words xs k (i + 1) := by
  apply Array.ext (by simp [overlay_size]) fun j h1 _ => ?_
  rw [Array.getElem_set]
  simp only [overlay, Array.getElem_ofFn]
  by_cases hj : k + i = j
  · subst hj
    rw [ite_eq_left rfl, ite_eq_left (by omega), Nat.add_sub_cancel_left, getElem!_pos xs i hi]
  · rw [ite_eq_right hj]
    by_cases hin : k ≤ j ∧ j < k + i
    · rw [ite_eq_left hin, ite_eq_left (by omega)]
    · rw [ite_eq_right hin, ite_eq_right (by omega)]

/-- The address of element `k + i` of the array at `ptr`, from `ptr + 8 * k` and `i`. -/
theorem element_address_at (ptr : UInt64) (k i : Nat) :
    (ptr + UInt64.ofNat (8 * k) + (UInt64.ofNat i + 1) * 8).toUInt32 =
      UInt64Array.wordAddress ptr (k + i + 1) := by
  unfold UInt64Array.wordAddress
  congr 1
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- The copy loop: the elements of the array `xs`, readable at `psrc`, go to elements `k` on of
the array `words` at `pdst`, whose address plus `8 * k` local `dst` holds.  The loop writes only
inside the region of `words`, which lies apart from that of `xs`, and changes no local but
`index`. -/
theorem wp_copyInto {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {src dst count index : Nat} {psrc pdst : UInt64} {xs words : Array UInt64} {k : Nat}
    {rest : Program} {Q : Assertion Unit}
    (hSrcA : UInt64Array.At store psrc xs) (hDstA : UInt64Array.At store pdst words)
    (hFit : k + xs.size ≤ words.size)
    (hApart : psrc.toNat + 8 * (xs.size + 1) ≤ pdst.toNat ∨
      pdst.toNat + 8 * (words.size + 1) ≤ psrc.toNat)
    (hSrc : s.get src = some (.i64 psrc))
    (hDst : s.get dst = some (.i64 (pdst + UInt64.ofNat (8 * k))))
    (hCount : s.get count = some (.i64 (UInt64.ofNat xs.size)))
    (hSrcI : src ≠ index) (hDstI : dst ≠ index) (hCountI : count ≠ index)
    (hLow : s.params.length ≤ index) (hHigh : index < s.params.length + s.locals.length)
    (hNext : ∀ (store' : Store Unit) (s' : Locals),
      Memory.WritesRange store store' pdst.toNat (pdst.toNat + 8 * (words.size + 1)) →
      UInt64Array.At store' pdst (overlay words xs k xs.size) →
      s'.params = s.params → s'.locals.length = s.locals.length →
      (∀ j, j ≠ index → s'.get j = s.get j) → s'.values = s.values →
      wp m rest Q store' s' host) :
    wp m (copyIntoCode src dst count index ++ rest) Q store s host := by
  have hSrcFit := hSrcA.1
  have hDstFit := hDstA.1
  simp only [copyIntoCode, List.cons_append, List.nil_append, wp_constI64_cons]
  refine wp_localSet_local (s := s) (vs := s.values) hLow hHigh ?_
  have hLow0 : ({ s with values := s.values } : Locals).params.length ≤ index := hLow
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st si => ∃ i, i ≤ xs.size ∧
      Memory.WritesRange store st pdst.toNat (pdst.toNat + 8 * (words.size + 1)) ∧
      UInt64Array.At st pdst (overlay words xs k i) ∧ si.params = s.params ∧
      si.locals.length = s.locals.length ∧ (∀ j, j ≠ index → si.get j = s.get j) ∧
      si.get index = some (.i64 (UInt64.ofNat i)))
    (fun _ si => match si.get index with
      | some (.i64 i) => xs.size - i.toNat
      | _ => 0)
    ⟨0, Nat.zero_le _, Memory.WritesRange.refl .., by rw [overlay_zero]; exact hDstA, rfl,
      by simp [setLocal], fun j hj => Locals.get_setLocal_ne hLow0 hj,
      Locals.get_setLocal_same hLow0 hHigh⟩ ?_
  rintro st si ⟨i, hi, hW, hA, hp, hl, hOther, hIdx⟩
  have hi64 : (UInt64.ofNat i).toNat = i :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hN64 : (UInt64.ofNat xs.size).toNat = xs.size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  simp only [wp_localGet_cons, Locals.get_values, hIdx, hOther count hCountI, hCount,
    wp_geUI64_cons, wp_br_if_cons]
  by_cases hDone : UInt64.ofNat xs.size ≤ UInt64.ofNat i
  · -- The copy is complete.
    have hiEq : i = xs.size := by
      rw [UInt64.le_iff_toNat_le, hi64, hN64] at hDone; omega
    subst hiEq
    simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    exact hNext st _ hW hA hp hl (fun j hj => hOther j hj) rfl
  · -- One more element.
    have hLess : i < xs.size := by
      rw [UInt64.le_iff_toNat_le, hi64, hN64] at hDone; omega
    simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte]
    have hSrcAt := hSrcA.writesRange hW (by omega)
    have hSrcElement := hSrcAt.elementBound i hLess
    have hki : k + i < (overlay words xs k i).size := by rw [overlay_size]; omega
    have hDstElement := hA.elementBound (k + i) hki
    simp only [wp_localGet_cons, Locals.get_values, hOther dst hDstI, hDst, hIdx,
      hOther src hSrcI, hSrc, wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons, wp_wrapI64_cons,
      wrap_toUInt32, element_address_at]
    simp only [element_address, wp_load64_cons, wp_store64_cons, UInt32.toNat_zero, Nat.add_zero,
      UInt32.add_zero]
    have hRead : st.mem.read64 (UInt64Array.wordAddress psrc (i + 1)) = xs[i] :=
      hSrcAt.elementRead i hLess
    rw [ite_eq_right (show ¬((UInt64Array.wordAddress psrc (i + 1)).toNat + 8 >
        st.mem.pages * 65536) by rw [UInt64Array.wordAddress]; omega),
      ite_eq_right (show ¬((UInt64Array.wordAddress pdst (k + i + 1)).toNat + 8 >
        st.mem.pages * 65536) by rw [UInt64Array.wordAddress]; omega), hRead]
    simp only [wp_localGet_cons, hIdx, wp_constI64_cons, wp_addI64_cons]
    have hLowI : si.params.length ≤ index := by rw [hp]; exact hLow
    have hHighI : index < si.params.length + si.locals.length := by rw [hp, hl]; exact hHigh
    refine wp_localSet_local (s := si) (vs := si.values) hLowI hHighI ?_
    rw [wp_br_cons]
    dsimp only
    have hLowI' : ({ si with values := si.values } : Locals).params.length ≤ index := hLowI
    have hSucc : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
      rw [UInt64.ofNat_add]; rfl
    have hSucc64 : (UInt64.ofNat (i + 1)).toNat = i + 1 :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    refine ⟨⟨i + 1, hLess, hW.trans (UInt64Array.writeElement_frame st pdst words.size (k + i)
      xs[i] hDstFit (by omega)), ?_, hp, by simp [setLocal, hl], fun j hj => ?_, ?_⟩, ?_⟩
    · rw [← overlay_succ (by omega) hLess]
      exact hA.writeElement hki xs[i]
    · rw [Locals.get_values, Locals.get_setLocal_ne hLowI' hj, Locals.get_values]
      exact hOther j hj
    · rw [Locals.get_setLocal_same hLowI' hHighI, hSucc]
    · simp only [Locals.get_setLocal_same hLowI' hHighI, hSucc, hSucc64, hi64]
      omega

/-- `ws` with the words from position `lo` to position `hi` moved up by `k`: positions `lo + k` to
`hi + k` hold the old words `lo` to `hi`, and the other positions keep theirs. -/
def shiftUp (ws : Array UInt64) (lo hi k : Nat) : Array UInt64 :=
  Array.ofFn (n := ws.size) fun j =>
    if lo + k ≤ j.val ∧ j.val < hi + k then ws[j.val - k]! else ws[j.val]

theorem shiftUp_size (ws : Array UInt64) (lo hi k : Nat) : (shiftUp ws lo hi k).size = ws.size :=
  Array.size_ofFn

theorem shiftUp_self (ws : Array UInt64) (hi k : Nat) : shiftUp ws hi hi k = ws := by
  apply Array.ext (shiftUp_size ..) fun j _ _ => ?_
  simp only [shiftUp, Array.getElem_ofFn]
  rw [ite_eq_right (by omega)]

theorem shiftUp_step {ws : Array UInt64} {t hi k : Nat} (ht : 0 < t) (hFit : hi + k ≤ ws.size)
    (hth : t ≤ hi) :
    (shiftUp ws t hi k).set (t - 1 + k) ws[t - 1]! (by rw [shiftUp_size]; omega) =
      shiftUp ws (t - 1) hi k := by
  apply Array.ext (by simp [shiftUp_size]) fun j h1 _ => ?_
  rw [Array.getElem_set]
  simp only [shiftUp, Array.getElem_ofFn]
  by_cases hj : t - 1 + k = j
  · subst hj
    rw [ite_eq_left rfl, ite_eq_left (by omega), show t - 1 + k - k = t - 1 by omega]
  · rw [ite_eq_right hj]
    by_cases hin : t + k ≤ j ∧ j < hi + k
    · rw [ite_eq_left hin, ite_eq_left (by omega)]
    · rw [ite_eq_right hin, ite_eq_right (by omega)]

/-- `ws` with the `n` words from position `lo + k` on moved down by `k`, to positions `lo` to
`lo + n`, and the other positions keeping theirs. -/
def shiftDown (ws : Array UInt64) (lo n k : Nat) : Array UInt64 :=
  Array.ofFn (n := ws.size) fun j =>
    if lo ≤ j.val ∧ j.val < lo + n then ws[j.val + k]! else ws[j.val]

theorem shiftDown_size (ws : Array UInt64) (lo n k : Nat) : (shiftDown ws lo n k).size = ws.size :=
  Array.size_ofFn

theorem shiftDown_zero (ws : Array UInt64) (lo k : Nat) : shiftDown ws lo 0 k = ws := by
  apply Array.ext (shiftDown_size ..) fun j _ _ => ?_
  simp only [shiftDown, Array.getElem_ofFn]
  rw [ite_eq_right (by omega)]

theorem shiftDown_succ {ws : Array UInt64} {lo i k : Nat} (hFit : lo + i + k < ws.size) :
    (shiftDown ws lo i k).set (lo + i) ws[lo + k + i]! (by rw [shiftDown_size]; omega) =
      shiftDown ws lo (i + 1) k := by
  apply Array.ext (by simp [shiftDown_size]) fun j h1 _ => ?_
  rw [Array.getElem_set]
  simp only [shiftDown, Array.getElem_ofFn]
  by_cases hj : lo + i = j
  · subst hj
    rw [ite_eq_left rfl, ite_eq_left (by omega), show lo + k + i = lo + i + k by omega]
  · rw [ite_eq_right hj]
    by_cases hin : lo ≤ j ∧ j < lo + i
    · rw [ite_eq_left hin, ite_eq_left (by omega)]
    · rw [ite_eq_right hin, ite_eq_right (by omega)]

theorem shiftUp_getElem! (ws : Array UInt64) (lo hi k : Nat) {j : Nat} (hj : j < ws.size) :
    (shiftUp ws lo hi k)[j]! = if lo + k ≤ j ∧ j < hi + k then ws[j - k]! else ws[j]! := by
  rw [getElem!_pos _ j (by rw [shiftUp_size]; exact hj), getElem!_pos ws j hj]
  simp only [shiftUp, Array.getElem_ofFn]

theorem shiftDown_getElem! (ws : Array UInt64) (lo n k : Nat) {j : Nat} (hj : j < ws.size) :
    (shiftDown ws lo n k)[j]! = if lo ≤ j ∧ j < lo + n then ws[j + k]! else ws[j]! := by
  rw [getElem!_pos _ j (by rw [shiftDown_size]; exact hj), getElem!_pos ws j hj]
  simp only [shiftDown, Array.getElem_ofFn]

theorem extract_getElem! (ws : Array UInt64) {n j : Nat} (hj : j < n) (hn : n ≤ ws.size) :
    (ws.extract 0 n)[j]! = ws[j]! := by
  rw [getElem!_pos _ j (by simp only [Array.size_extract]; omega), getElem!_pos ws j (by omega)]
  simp [Array.getElem_extract]

/-- The words of an array with room for one more element, with the words from element `i` on
moved up by one element and the new element's words written at element `i`, are the words of the
array with the element inserted at `i`. -/
theorem Elem.words_insertIdx (e : Elem) {xs : Array e.denote} {ws : Array UInt64} (v : e.denote)
    {i : Nat} (hi : i ≤ xs.size) (hSize : ws.size = xs.size * e.width + e.width)
    (hPrefix : ∀ w, w < xs.size * e.width → ws[w]! = (e.words xs)[w]!) :
    writeWords (shiftUp ws (i * e.width) (xs.size * e.width) e.width) (i * e.width)
      (e.toWords v) = e.words (xs.insertIdx i v hi) := by
  have hk := e.width_pos
  have hik : i * e.width ≤ xs.size * e.width := Nat.mul_le_mul_right _ hi
  apply Elem.words_ext e (by rw [writeWords_size, shiftUp_size, hSize, Array.size_insertIdx,
    Nat.succ_mul])
  intro i' hi' j hj
  rw [Array.size_insertIdx] at hi'
  have hpos : i' * e.width + j < xs.size * e.width + e.width := by
    have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hi')
    rw [Nat.succ_mul, Nat.succ_mul] at this; omega
  rw [writeWords_getElem! _ _ _ (by rw [e.toWords_length, shiftUp_size, hSize]; omega),
    e.toWords_length, getElem!_pos (xs.insertIdx i v hi) i' (by rw [Array.size_insertIdx]; omega),
    Array.getElem_insertIdx]
  rcases Nat.lt_trichotomy i' i with hlt | heq | hgt
  · have hw : i' * e.width + j < i * e.width := by
      have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_mul] at this; omega
    rw [if_neg (by omega), shiftUp_getElem! _ _ _ _ (by rw [hSize]; omega), if_neg (by omega),
      hPrefix _ (by omega), Elem.words_getElem! e xs (by omega) hj, dite_eq_left hlt]
  · subst heq
    rw [if_pos (by omega), show i' * e.width + j - i' * e.width = j by omega,
      dite_eq_right (by omega), dite_eq_left rfl]
  · have hw : i * e.width + e.width ≤ i' * e.width + j := by
      have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hgt)
      rw [Nat.succ_mul] at this; omega
    have hi1 : i' - 1 < xs.size := by omega
    have hsplit : i' * e.width + j - e.width = (i' - 1) * e.width + j := by
      rw [Nat.sub_mul, Nat.one_mul]
      have : e.width ≤ i' * e.width := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rw [if_neg (by omega), shiftUp_getElem! _ _ _ _ (by rw [hSize]; omega), if_pos (by omega),
      hsplit, hPrefix _ (by
        have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hi1)
        rw [Nat.succ_mul] at this; omega),
      Elem.words_getElem! e xs hi1 hj, dite_eq_right (by omega), dite_eq_right (by omega)]

/-- The words of an array with the words after element `i` moved down by one element, cut to
one element fewer, are the words of the array without element `i`. -/
theorem Elem.words_eraseIdx (e : Elem) {xs : Array e.denote} {i : Nat} (hi : i < xs.size) :
    (shiftDown (e.words xs) (i * e.width) (xs.size * e.width - i * e.width - e.width)
      e.width).extract 0 (xs.size * e.width - e.width) = e.words (xs.eraseIdx i hi) := by
  have hk := e.width_pos
  have hik : i * e.width + e.width ≤ xs.size * e.width := by
    have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at this; omega
  apply Elem.words_ext e (by
    rw [Array.size_extract, shiftDown_size, Elem.words_size, Array.size_eraseIdx, Nat.sub_mul,
      Nat.one_mul]; omega)
  intro i' hi' j hj
  rw [Array.size_eraseIdx] at hi'
  have hi1 : i' + 1 < xs.size := by omega
  have hpos : i' * e.width + j + e.width < xs.size * e.width := by
    have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hi1)
    rw [Nat.succ_mul, Nat.succ_mul] at this; omega
  rw [extract_getElem! _ (by omega) (by rw [shiftDown_size, Elem.words_size]; omega),
    shiftDown_getElem! _ _ _ _ (by rw [Elem.words_size]; omega),
    getElem!_pos (xs.eraseIdx i hi) i' (by rw [Array.size_eraseIdx]; omega),
    Array.getElem_eraseIdx]
  by_cases hlt : i' < i
  · have hw : i' * e.width + j < i * e.width := by
      have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_mul] at this; omega
    rw [if_neg (by omega), Elem.words_getElem! e xs (by omega) hj, dite_eq_left hlt]
  · have hw : i * e.width ≤ i' * e.width := Nat.mul_le_mul_right _ (by omega)
    rw [if_pos (by omega), show i' * e.width + j + e.width = (i' + 1) * e.width + j by
      rw [Nat.succ_mul]; omega, Elem.words_getElem! e xs hi1 hj, dite_eq_right hlt]

/-- The first words of an array with room, up to its old length, are the old words. -/
theorem Elem.words_extract_prefix (e : Elem) {xs : Array e.denote} {ws : Array UInt64}
    (hSize : xs.size * e.width ≤ ws.size)
    (hPrefix : ∀ w, w < xs.size * e.width → ws[w]! = (e.words xs)[w]!) :
    ws.extract 0 (xs.size * e.width) = e.words xs := by
  apply Array.ext (by rw [Array.size_extract, Elem.words_size]; omega) fun w h1 h2 => ?_
  have hw : w < xs.size * e.width := by rw [Elem.words_size] at h2; exact h2
  rw [← getElem!_pos _ w h1, ← getElem!_pos (e.words xs) w h2, extract_getElem! _ hw hSize]
  exact hPrefix w hw

/-- The address of word `i + k + 1` of the array at `ptr`, from `i` and `k + 1`. -/
theorem element_address_up (ptr : UInt64) (i k : Nat) :
    (ptr + (UInt64.ofNat i + UInt64.ofNat (k + 1)) * 8).toUInt32 =
      UInt64Array.wordAddress ptr (i + k + 1) := by
  unfold UInt64Array.wordAddress
  congr 1
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- The loop of `shiftUpCode`: in the array `ws` at `p`, whose address local `ptr` holds, the words
from position `l`, in local `lo`, to position `h`, in local `index`, move up by `k`.  The loop
writes only inside the region of `ws` and changes no local but `index`. -/
theorem wp_shiftUp {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {ptr lo index k : Nat} {p : UInt64} {ws : Array UInt64} {l h : Nat}
    {rest : Program} {Q : Assertion Unit}
    (hA : UInt64Array.At store p ws) (hlh : l ≤ h) (hFit : h + k ≤ ws.size)
    (hP : s.get ptr = some (.i64 p)) (hLo : s.get lo = some (.i64 (UInt64.ofNat l)))
    (hIdx : s.get index = some (.i64 (UInt64.ofNat h)))
    (hPI : ptr ≠ index) (hLI : lo ≠ index)
    (hLow : s.params.length ≤ index) (hHigh : index < s.params.length + s.locals.length)
    (hNext : ∀ (store' : Store Unit) (s' : Locals),
      Memory.WritesRange store store' p.toNat (p.toNat + 8 * (ws.size + 1)) →
      UInt64Array.At store' p (shiftUp ws l h k) →
      s'.params = s.params → s'.locals.length = s.locals.length →
      (∀ j, j ≠ index → s'.get j = s.get j) → s'.values = s.values →
      wp m rest Q store' s' host) :
    wp m (shiftUpCode ptr lo index k ++ rest) Q store s host := by
  have hFitA := hA.1
  have hl64 : (UInt64.ofNat l).toNat = l :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  simp only [shiftUpCode, List.cons_append, List.nil_append]
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st si => ∃ t, l ≤ t ∧ t ≤ h ∧
      Memory.WritesRange store st p.toNat (p.toNat + 8 * (ws.size + 1)) ∧
      UInt64Array.At st p (shiftUp ws t h k) ∧ si.params = s.params ∧
      si.locals.length = s.locals.length ∧ (∀ j, j ≠ index → si.get j = s.get j) ∧
      si.get index = some (.i64 (UInt64.ofNat t)))
    (fun _ si => match si.get index with
      | some (.i64 i) => i.toNat
      | _ => 0)
    ⟨h, hlh, le_rfl, Memory.WritesRange.refl .., by rw [shiftUp_self]; exact hA, rfl, rfl,
      fun _ _ => rfl, hIdx⟩ ?_
  rintro st si ⟨t, hlt, hth, hW, hAt, hp, hl, hOther, hT⟩
  have ht64 : (UInt64.ofNat t).toNat = t :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  simp only [wp_localGet_cons, Locals.get_values, hT, hOther lo hLI, hLo, wp_leUI64_cons,
    wp_br_if_cons]
  by_cases hDone : UInt64.ofNat t ≤ UInt64.ofNat l
  · -- The move is complete.
    have htEq : t = l := by
      rw [UInt64.le_iff_toNat_le, ht64, hl64] at hDone; omega
    subst htEq
    simp (config := { decide := true }) only [hDone, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    exact hNext st _ hW hAt hp hl (fun j hj => hOther j hj) rfl
  · -- One more word.
    have hLess : l < t := by
      rw [UInt64.le_iff_toNat_le, ht64, hl64] at hDone; omega
    simp (config := { decide := true }) only [hDone, ↓reduceIte]
    have hPred : UInt64.ofNat t - 1 = UInt64.ofNat (t - 1) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, ht64]; simp only [UInt64.reduceToNat]; omega), ht64]
      rw [UInt64.toNat_ofNat_of_lt'
        (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
      simp only [UInt64.reduceToNat]
    simp only [wp_localGet_cons, Locals.get_values, hT, wp_constI64_cons, wp_subI64_cons, hPred]
    have hLowI : si.params.length ≤ index := by rw [hp]; exact hLow
    have hHighI : index < si.params.length + si.locals.length := by rw [hp, hl]; exact hHigh
    refine wp_localSet_local (s := si) (vs := si.values) hLowI hHighI ?_
    have hLowI' : ({ si with values := si.values } : Locals).params.length ≤ index := hLowI
    have hGetI := Locals.get_setLocal_same hLowI' hHighI (v := .i64 (UInt64.ofNat (t - 1)))
    have hGetP : (setLocal { si with values := si.values } index
        (.i64 (UInt64.ofNat (t - 1)))).get ptr = some (.i64 p) := by
      rw [Locals.get_setLocal_ne hLowI' hPI, Locals.get_values, hOther ptr hPI, hP]
    have hRd : t - 1 < (shiftUp ws t h k).size := by rw [shiftUp_size]; omega
    have hWr : t - 1 + k < (shiftUp ws t h k).size := by rw [shiftUp_size]; omega
    have hSrcElement := hAt.elementBound (t - 1) hRd
    have hDstElement := hAt.elementBound (t - 1 + k) hWr
    simp only [wp_localGet_cons, Locals.get_values, hGetP, hGetI, wp_constI64_cons,
      wp_addI64_cons, wp_mulI64_cons, wp_wrapI64_cons, wrap_toUInt32, element_address_up,
      element_address]
    simp only [wp_load64_cons, wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    have hRead : st.mem.read64 (UInt64Array.wordAddress p (t - 1 + 1)) = ws[t - 1]! := by
      have h2 : (shiftUp ws t h k)[t - 1]'hRd = ws[t - 1]! := by
        simp only [shiftUp, Array.getElem_ofFn]
        rw [ite_eq_right (by omega)]
        exact (getElem!_pos ws _ (by omega)).symm
      exact (hAt.elementRead (t - 1) hRd).trans h2
    rw [ite_eq_right (show ¬((UInt64Array.wordAddress p (t - 1 + 1)).toNat + 8 >
        st.mem.pages * 65536) by rw [UInt64Array.wordAddress]; omega),
      ite_eq_right (show ¬((UInt64Array.wordAddress p (t - 1 + k + 1)).toNat + 8 >
        st.mem.pages * 65536) by rw [UInt64Array.wordAddress]; omega), hRead]
    rw [wp_br_cons]
    dsimp only
    refine ⟨⟨t - 1, by omega, by omega, hW.trans (UInt64Array.writeElement_frame st p ws.size
      (t - 1 + k) ws[t - 1]! hFitA (by omega)), ?_, hp, by simp [setLocal, hl], fun j hj => ?_,
      by rw [Locals.get_values]; exact hGetI⟩, ?_⟩
    · rw [← shiftUp_step (by omega) hFit hth]
      exact hAt.writeElement hWr ws[t - 1]!
    · rw [Locals.get_values, Locals.get_setLocal_ne hLowI' hj, Locals.get_values]
      exact hOther j hj
    · simp only [Locals.get_values, hGetI, ht64]
      rw [UInt64.toNat_ofNat_of_lt'
        (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
      omega

/-- The loop of `copyIntoCode` inside one array: in the array `ws` at `p`, the `n` words from
position `l + k` on move down by `k`, with `p + 8 (l + k)` in local `src` and `p + 8 l` in local
`dst`.  Each word is read before the loop writes it, since the writes trail the reads.  The loop
writes only inside the region of `ws` and changes no local but `index`. -/
theorem wp_copyDown {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {src dst count index : Nat} {p : UInt64} {ws : Array UInt64} {l n k : Nat}
    {rest : Program} {Q : Assertion Unit}
    (hA : UInt64Array.At store p ws) (hFit : l + n + k ≤ ws.size)
    (hSrc : s.get src = some (.i64 (p + UInt64.ofNat (8 * (l + k)))))
    (hDst : s.get dst = some (.i64 (p + UInt64.ofNat (8 * l))))
    (hCount : s.get count = some (.i64 (UInt64.ofNat n)))
    (hSrcI : src ≠ index) (hDstI : dst ≠ index) (hCountI : count ≠ index)
    (hLow : s.params.length ≤ index) (hHigh : index < s.params.length + s.locals.length)
    (hNext : ∀ (store' : Store Unit) (s' : Locals),
      Memory.WritesRange store store' p.toNat (p.toNat + 8 * (ws.size + 1)) →
      UInt64Array.At store' p (shiftDown ws l n k) →
      s'.params = s.params → s'.locals.length = s.locals.length →
      (∀ j, j ≠ index → s'.get j = s.get j) → s'.values = s.values →
      wp m rest Q store' s' host) :
    wp m (copyIntoCode src dst count index ++ rest) Q store s host := by
  have hFitA := hA.1
  simp only [copyIntoCode, List.cons_append, List.nil_append, wp_constI64_cons]
  refine wp_localSet_local (s := s) (vs := s.values) hLow hHigh ?_
  have hLow0 : ({ s with values := s.values } : Locals).params.length ≤ index := hLow
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st si => ∃ i, i ≤ n ∧
      Memory.WritesRange store st p.toNat (p.toNat + 8 * (ws.size + 1)) ∧
      UInt64Array.At st p (shiftDown ws l i k) ∧ si.params = s.params ∧
      si.locals.length = s.locals.length ∧ (∀ j, j ≠ index → si.get j = s.get j) ∧
      si.get index = some (.i64 (UInt64.ofNat i)))
    (fun _ si => match si.get index with
      | some (.i64 i) => n - i.toNat
      | _ => 0)
    ⟨0, Nat.zero_le _, Memory.WritesRange.refl .., by rw [shiftDown_zero]; exact hA, rfl,
      by simp [setLocal], fun j hj => Locals.get_setLocal_ne hLow0 hj,
      Locals.get_setLocal_same hLow0 hHigh⟩ ?_
  rintro st si ⟨i, hi, hW, hAt, hp, hl, hOther, hIdx⟩
  have hi64 : (UInt64.ofNat i).toNat = i :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hN64 : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  simp only [wp_localGet_cons, Locals.get_values, hIdx, hOther count hCountI, hCount,
    wp_geUI64_cons, wp_br_if_cons]
  by_cases hDone : UInt64.ofNat n ≤ UInt64.ofNat i
  · -- The move is complete.
    have hiEq : i = n := by
      rw [UInt64.le_iff_toNat_le, hi64, hN64] at hDone; omega
    subst hiEq
    simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    exact hNext st _ hW hAt hp hl (fun j hj => hOther j hj) rfl
  · -- One more word.
    have hLess : i < n := by
      rw [UInt64.le_iff_toNat_le, hi64, hN64] at hDone; omega
    simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte]
    have hRd : l + k + i < (shiftDown ws l i k).size := by rw [shiftDown_size]; omega
    have hWr : l + i < (shiftDown ws l i k).size := by rw [shiftDown_size]; omega
    have hSrcElement := hAt.elementBound (l + k + i) hRd
    have hDstElement := hAt.elementBound (l + i) hWr
    simp only [wp_localGet_cons, Locals.get_values, hOther dst hDstI, hDst, hIdx,
      hOther src hSrcI, hSrc, wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons, wp_wrapI64_cons,
      wrap_toUInt32, element_address_at]
    simp only [wp_load64_cons, wp_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    have hRead : st.mem.read64 (UInt64Array.wordAddress p (l + k + i + 1)) = ws[l + k + i]! := by
      have h2 : (shiftDown ws l i k)[l + k + i]'hRd = ws[l + k + i]! := by
        simp only [shiftDown, Array.getElem_ofFn]
        rw [ite_eq_right (by omega)]
        exact (getElem!_pos ws _ (by omega)).symm
      exact (hAt.elementRead (l + k + i) hRd).trans h2
    rw [ite_eq_right (show ¬((UInt64Array.wordAddress p (l + k + i + 1)).toNat + 8 >
        st.mem.pages * 65536) by rw [UInt64Array.wordAddress]; omega),
      ite_eq_right (show ¬((UInt64Array.wordAddress p (l + i + 1)).toNat + 8 >
        st.mem.pages * 65536) by rw [UInt64Array.wordAddress]; omega), hRead]
    simp only [wp_localGet_cons, hIdx, wp_constI64_cons, wp_addI64_cons]
    have hLowI : si.params.length ≤ index := by rw [hp]; exact hLow
    have hHighI : index < si.params.length + si.locals.length := by rw [hp, hl]; exact hHigh
    refine wp_localSet_local (s := si) (vs := si.values) hLowI hHighI ?_
    rw [wp_br_cons]
    dsimp only
    have hLowI' : ({ si with values := si.values } : Locals).params.length ≤ index := hLowI
    have hSucc : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
      rw [UInt64.ofNat_add]; rfl
    have hSucc64 : (UInt64.ofNat (i + 1)).toNat = i + 1 :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    refine ⟨⟨i + 1, hLess, hW.trans (UInt64Array.writeElement_frame st p ws.size (l + i)
      ws[l + k + i]! hFitA (by omega)), ?_, hp, by simp [setLocal, hl], fun j hj => ?_, ?_⟩, ?_⟩
    · rw [← shiftDown_succ (by omega)]
      exact hAt.writeElement hWr ws[l + k + i]!
    · rw [Locals.get_values, Locals.get_setLocal_ne hLowI' hj, Locals.get_values]
      exact hOther j hj
    · rw [Locals.get_setLocal_same hLowI' hHighI, hSucc]
    · simp only [Locals.get_setLocal_same hLowI' hHighI, hSucc, hSucc64, hi64]
      omega

/-- An array after a write of a length `n` no larger than its own: its first `n` words. -/
theorem _root_.LeanExe.ProofKit.UInt64Array.At.writeLength {store : Store Unit} {ptr : UInt64}
    {values : Array UInt64} (h : UInt64Array.At store ptr values) {n : Nat}
    (hn : n ≤ values.size) :
    UInt64Array.At { store with mem := store.mem.write64 ptr.toUInt32 (UInt64.ofNat n) } ptr
      (values.extract 0 n) := by
  have hFit := h.1
  have hMem := h.2.1
  have hP := h.pointerAddress_toNat
  have hsz : (values.extract 0 n).size = n := by simp only [Array.size_extract]; omega
  refine ⟨by rw [hsz]; omega, ?_, ?_, fun j hj => ?_⟩
  · rw [hsz]; show _ ≤ (store.mem.write64 _ _).pages * 65536
    rw [Mem.write64_pages]; omega
  · show (store.mem.write64 _ _).read64 _ = _
    rw [Memory.read64_write64, hsz]
  · have hj' : j < n := by rw [hsz] at hj; exact hj
    show (store.mem.write64 ptr.toUInt32 _).read64 _ = _
    rw [Memory.read64_write64_disjoint store.mem _ _ _ (Or.inr (by
      rw [h.elementAddress_toNat j (by omega), hP]; omega)), h.elementRead j (by omega)]
    simp [Array.getElem_extract]

theorem writeLength_frame (store : Store Unit) (ptr : UInt64) (size n : Nat)
    (hFit : ptr.toNat + 8 * (size + 1) ≤ 4294967296) :
    Memory.WritesRange store { store with mem := store.mem.write64 ptr.toUInt32 (UInt64.ofNat n) }
      ptr.toNat (ptr.toNat + 8 * (size + 1)) := by
  apply Memory.WritesRange.write64
  · rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]; omega

/-- The allocation of a block of the byte count on top of the stack for an array of `total` words,
with `total` in local `len`, and the copy into it of the array `xs`, borrowed at `ptr`, whose
address local `src` holds and whose length local `count` holds: a new owned block, with its address
in local `dst`, holding an array of `total` words whose first elements are those of `xs`.  The
allocation may trap at `unreachable` when memory runs out. -/
theorem wp_allocCopy {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {src len count dst index : Nat} {ptr total bytes : UInt64}
    {xs : Array UInt64} {vs : List Value} {rest : Program} {Q : Assertion Unit} {c : Nat}
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hc : allocCost (allocSize bytes).toNat ≤ c) (hTrap : TrapOK (!decide (heap.Within store m c)) Q)
    (hB : heap.Borrowed store ptr xs) (hTotal : total.toNat < 536870912)
    (hn : xs.size ≤ total.toNat) (hBytes : 8 * (total.toNat + 1) ≤ bytes.toNat)
    (hBytes32 : bytes.toNat ≤ 4294967296) (hSrc : s.get src = some (.i64 ptr))
    (hLen : s.get len = some (.i64 total))
    (hCount : s.get count = some (.i64 (UInt64.ofNat xs.size)))
    (hDst : s.params.length ≤ dst) (hDstHigh : dst < s.params.length + s.locals.length)
    (hIndex : s.params.length ≤ index) (hIndexHigh : index < s.params.length + s.locals.length)
    (hSrcDst : src ≠ dst) (hLenDst : len ≠ dst) (hCountDst : count ≠ dst)
    (hSrcIndex : src ≠ index) (hDstIndex : dst ≠ index) (hCountIndex : count ≠ index)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (q : UInt64)
      (words : Array UInt64), words.size = total.toNat →
      (∀ j (hj : j < xs.size), words[j]! = xs[j]) →
      Step heap store (fun _ => True) heap' store' [block store' q] → heap'.Owned store' q words →
      bytes.toNat ≤ capacityAt store' q → s'.params = s.params →
      s'.locals.length = s.locals.length → (∀ j, j ≠ dst → j ≠ index → s'.get j = s.get j) →
      s'.get dst = some (.i64 q) → s'.values = vs → heap'.top.toNat ≤ heap.top.toNat + c →
      wp m rest Q store' s' host) :
    wp m (allocBlockCode len dst ++ (copyIntoCode src dst count index ++ rest)) Q store
      { s with values := .i64 bytes :: vs } host := by
  have hFitA := hB.values.1
  refine wp_allocBlock hm hAt hCap hc hTrap hTotal hBytes hBytes32 hLen hDst hDstHigh hLenDst
    fun heap1 store1 q words0 hSize0 hStep1 hOwned1 hCapQ hTop => ?_
  have hLow1 : ({ s with values := vs } : Locals).params.length ≤ dst := hDst
  have hQ1 : (setLocal { s with values := vs } dst (.i64 q)).get dst = some (.i64 q) :=
    Locals.get_setLocal_same hLow1 hDstHigh
  have hGet1 : ∀ j, j ≠ dst → (setLocal { s with values := vs } dst (.i64 q)).get j = s.get j :=
    fun j hj => Locals.get_setLocal_ne hLow1 hj
  -- The source stays readable, apart from the new block.
  obtain ⟨hB1, hApart1⟩ := hStep1.borrowed hB trivial
  have hApart := hApart1 _ (List.mem_singleton_self _)
  have hCapacity := hOwned1.capacity
  have hRootBase := hOwned1.base
  simp only [block, regionsDisjoint] at hApart
  refine wp_copyInto (k := 0) hB1.values hOwned1.values (by omega) (by rw [hSize0]; omega)
    (by rw [hGet1 src hSrcDst]; exact hSrc) (by simpa using hQ1)
    (by rw [hGet1 count hCountDst]; exact hCount) hSrcIndex hDstIndex hCountIndex
    (by show s.params.length ≤ index; exact hIndex)
    (by show index < s.params.length + (setLocal _ dst _).locals.length
        simp [setLocal]; omega)
    fun store2 s2 hW hA2 hp2 hl2 hOther2 hv2 => ?_
  have hWithin : WritesWithin store1 store2 q.toNat (capacityAt store1 q) :=
    ⟨by rw [hW.1], hW.2.1, fun a ha => hW.2.2 a (by rw [hSize0] at hCapacity; omega)⟩
  obtain ⟨hOwned2, hCapSame⟩ := hOwned1.rewrite hWithin hA2
    (by rw [overlay_size, hSize0]; rw [hSize0] at hCapacity; exact hCapacity)
  have hBlock : block store2 q = block store1 q := block_eq hCapSame
  have hWrite : Step heap1 store1 (fun r => regionsDisjoint r (block store1 q)) heap1 store2 [] :=
    ⟨Heap.At.writesOwned hStep1.at_ hOwned1 hWithin, by rw [hW.1], fun r hr _ hd =>
      ⟨fun x hl hh => hWithin.bytes x (by simp only [block, regionsDisjoint] at hd; omega), hr,
        nofun⟩⟩
  have hStep := hStep1.transBoth hWrite (keep := fun _ => True)
    fun _ _ => ⟨trivial, fun hf => hf _ (List.mem_singleton_self _)⟩
  refine hNext heap1 store2 s2 q (overlay words0 xs 0 xs.size) (by rw [overlay_size, hSize0])
    (fun j hj => ?_) (hStep.mono (fun _ h => h) fun b hb => ?_) hOwned2
    (by rw [hCapSame]; exact hCapQ) hp2 (by rw [hl2]; simp [setLocal])
    (fun j hj hji => by rw [hOther2 j hji, hGet1 j hj])
    (by rw [hOther2 dst hDstIndex]; exact hQ1) hv2 hTop
  · rw [getElem!_pos _ j (by rw [overlay_size]; omega)]
    simp only [overlay, Array.getElem_ofFn]
    rw [ite_eq_left (by omega), Nat.sub_zero, getElem!_pos xs j hj]
  · rw [List.mem_singleton.mp hb, hBlock]
    exact List.mem_append_left _ (List.mem_singleton_self _)

/-- The byte count of a block for the length `t` in local `total`, given the capacity `c` in
local `cap`: at least the bytes that the length needs, at most `2 ^ 32`, and at most the larger of
those bytes and twice the capacity. -/
theorem wp_requestCode {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {total cap : Nat} {t c : UInt64} {rest : Program} {Q : Assertion Unit}
    (hT : s.get total = some (.i64 t)) (hC : s.get cap = some (.i64 c))
    (ht : t.toNat < 536870912) (hc : c.toNat < 4294967296)
    (hNext : ∀ r : UInt64, 8 * (t.toNat + 1) ≤ r.toNat → r.toNat ≤ 4294967296 →
      r.toNat ≤ max (8 * (t.toNat + 1)) (2 * c.toNat) →
      wp m rest Q store { s with values := .i64 r :: s.values } host) :
    wp m (requestCode total cap ++ rest) Q store s host := by
  have hNeed : ((t + 1) * 8).toNat = 8 * (t.toNat + 1) := by
    simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  have hDouble : (c * 2).toNat = 2 * c.toNat := by
    simp only [UInt64.toNat_mul, UInt64.reduceToNat]
    omega
  simp only [requestCode, List.cons_append, List.nil_append, wp_localGet_cons, Locals.get_values,
    hT, hC, wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons, wp_leUI64_cons]
  rw [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases h1 : (t + 1) * 8 ≤ c * 2
  · simp (config := { decide := true }) only [h1, ↓reduceIte]
    simp only [wp_localGet_cons, hC, wp_constI64_cons, wp_mulI64_cons, wp_leUI64_cons]
    rw [wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases h2 : c * 2 ≤ 4294967296
    · simp (config := { decide := true }) only [h2, ↓reduceIte]
      simp only [wp_localGet_cons, hC, wp_constI64_cons, wp_mulI64_cons, wp_nil]
      rw [UInt64.le_iff_toNat_le, hNeed] at h1
      rw [UInt64.le_iff_toNat_le] at h2
      simpa using hNext (c * 2) h1 h2 (by rw [hDouble]; omega)
    · simp (config := { decide := true }) only [h2, ↓reduceIte]
      simp only [wp_constI64_cons, wp_nil]
      rw [UInt64.le_iff_toNat_le, hNeed] at h1
      simpa using hNext 4294967296 (by simp only [UInt64.reduceToNat]; omega) (by decide)
        (by
          rw [UInt64.not_le, UInt64.lt_iff_toNat_lt, hDouble] at h2
          simp only [UInt64.reduceToNat] at h2 ⊢
          omega)
  · simp (config := { decide := true }) only [h1, ↓reduceIte]
    simp only [wp_localGet_cons, hT, wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons, wp_nil]
    simpa using hNext ((t + 1) * 8) (by rw [hNeed]) (by rw [hNeed]; omega) (by rw [hNeed]; omega)

/-- The copy of an array that is readable at `ptr`, whose address local `src` holds, into a new
owned array, with the locals from `base` to `base + 2` as scratch.  The copy allocates, so it may
trap at `unreachable`. -/
theorem wp_copyArray {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {src base : Nat} {ptr : UInt64} {xs : Array UInt64}
    {rest : Program} {Q : Assertion Unit} {c : Nat}
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hc : allocCost (8 * (xs.size + 1)) ≤ c) (hTrap : TrapOK (!decide (heap.Within store m c)) Q)
    (hB : heap.Borrowed store ptr xs) (hSrc : s.get src = some (.i64 ptr)) (hSrcBase : src < base)
    (hBase : s.params.length ≤ base) (hRoom : base + 3 ≤ s.half)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (ptr' : UInt64),
      Step heap store (fun _ => True) heap' store' [block store' ptr'] →
      heap'.Owned store' ptr' xs → Frame base s s' → heap'.top.toNat ≤ heap.top.toNat + c →
      wp m rest Q store' { s' with values := .i64 ptr' :: s.values } host) :
    wp m (copyArrayCode src base ++ rest) Q store s host := by
  have hTot : 2 * s.half ≤ s.params.length + s.locals.length := by
    simp only [Locals.half]; omega
  have hA := hB.values
  have hLen := hA.lengthBound
  have hFitA := hA.1
  have hSizeLt : xs.size < 536870912 := by omega
  have hN : (UInt64.ofNat xs.size).toNat = xs.size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  obtain ⟨hBytes, hAllocSize⟩ := allocSize_words hSizeLt
  simp only [copyArrayCode, allocArrayCode, List.append_assoc, List.cons_append,
    List.nil_append]
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
  -- The new array and its elements.
  show wp m _ Q store s1 host
  simp only [wp_localGet_cons, hN1, wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons]
  refine wp_allocCopy (c := c) hm hAt hCap (by rw [hAllocSize, hBytes]; exact hc) hTrap hB
    (by rw [hN]; exact hSizeLt) (by rw [hN])
    (by rw [hBytes]; rw [hN]) (by rw [hBytes]; omega) hSrc1 hN1 hN1
    (by show s.params.length ≤ base + 1; omega)
    (by show base + 1 < s1.params.length + s1.locals.length; simp [s1, setLocal]; omega)
    (by show s.params.length ≤ base + 2; omega)
    (by show base + 2 < s1.params.length + s1.locals.length; simp [s1, setLocal]; omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    fun heap1 store1 s2 q words hSize hPrefix hStep hOwned _ hp2 hl2 hOther2 hQ2 hv2 hTop => ?_
  have hWords : words = xs := by
    apply Array.ext (by rw [hSize, hN]) fun j h1 h2 => ?_
    rw [← getElem!_pos words j h1]
    exact hPrefix j h2
  subst hWords
  have hF : Frame base s s2 := by
    refine ⟨hp2, by rw [hl2]; simp [s1, setLocal], fun j hj => ⟨?_, ?_⟩⟩
    · rw [hOther2 j (by omega) (by omega)]
      show s1.get j = s.get j
      rw [Locals.get_setLocal_ne hLow1 (by omega), Locals.get_values]
    · rw [hOther2 _ (by omega) (by omega)]
      show s1.get _ = s.get _
      rw [Locals.get_setLocal_ne hLow1 (by omega), Locals.get_values]
  simp only [wp_localGet_cons, hQ2]
  have hv1 : s1.values = s.values := rfl
  simpa [hv2, hv1] using hNext heap1 store1 s2 q hStep hOwned hF hTop

/-- An assertion that accepts every trap at `unreachable` accepts those of any allowance. -/
theorem _root_.Wasm.TrapOK.any {b : Bool} {Q : Assertion Unit} (h : TrapOK true Q) : TrapOK b Q := by
  cases b
  · trivial
  · exact h

/-- An allowance for a trap when `top` cannot rise by `c` gives one for any `c'` whose room
follows from `c`'s. -/
theorem _root_.Wasm.TrapOK.within {P P' : Prop} [Decidable P] [Decidable P'] {Q : Assertion Unit}
    (h : TrapOK (!decide P) Q) (hP : P → P') : TrapOK (!decide P') Q := by
  by_cases hp' : P'
  · simp [hp', TrapOK]
  · have hp : ¬P := fun hp => hp' (hP hp)
    simpa [hp, hp'] using h

/-- Room for `c1 + c2` before a step that raises `top` by at most `c1` leaves room for `c2` after
it. -/
theorem _root_.LeanExe.Pipeline.Heap.Within.after {heap heap1 : Heap} {store store1 : Store Unit} {m : Module}
    {c1 c2 : Nat} (h : heap.Within store m (c1 + c2)) (hTop : heap1.top.toNat ≤ heap.top.toNat + c1)
    (hCaps : store1.memoryCap m 0 = store.memoryCap m 0) : heap1.Within store1 m c2 := by
  unfold Heap.Within at *; rw [hCaps]; omega

/-- The copy of a value of type `t` whose words locals `src` on hold and that its words represent
in `heap` at `store`: each of its arrays goes to a new owned block, and the other words stay as
they are.  The copy consumes nothing, raises `top` by at most `t.copyCost v`, and traps only when
`top` cannot rise by that much within the cap. -/
theorem wp_copyCode {m : Module} (hm : Runtime m) {host : HostEnv Unit} :
    (t : Ty) → ∀ {heap : Heap} {store : Store Unit} {s : Locals} {h src base : Nat} {mode : Mode}
      {ws : List Value} {v : t.denote} {rest : Program} {Q : Assertion Unit},
    heap.At store → store.memoryCap m 0 ≤ 65535 →
    TrapOK (!decide (heap.Within store m (t.copyCost v))) Q → s.half = h →
    t.Rep mode heap store ws v → LocalsHold s src t.types ws → src + t.width ≤ base →
    s.params.length ≤ base → base + t.copyScratch ≤ s.half →
    (∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (ws' : List Value),
      Step heap store (fun _ => True) heap' store' (t.blocks store' ws' v) →
      t.Rep .owned heap' store' ws' v → Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + t.copyCost v →
      wp m rest Q store' { s' with values := ws'.reverse ++ s.values } host) →
    wp m (copyCode h t src base ++ rest) Q store s host
  | .elem e, heap, store, s, h, src, base, mode, ws, v, rest, Q, hAt, _, _, hh, hRep, hold, _, _,
      _, hNext => by
    have hRep' : ws = e.values v := hRep
    subst hRep'
    simp only [copyCode]
    exact wp_loadCode _ (by rw [e.values_length, e.types_length]) hh hold
      (hNext heap store s _ (Step.refl hAt _) rfl (Frame.refl base s) (Nat.le_add_right _ _))
  | .array e, heap, store, s, h, src, base, mode, ws, v, rest, Q, hAt, hCap, hTrap, _, hRep, hold,
      hSrc, hBase, hRoom, hNext => by
    obtain ⟨ptr, rfl, ha⟩ := hRep
    have h0 : s.get src = some (.i64 ptr) := LocalsHold.word hold
    simp only [copyCode]
    exact wp_copyArray hm hAt hCap
      (by simp only [Elem.words_size, Ty.copyCost, allocCost]; omega) hTrap ha.borrow h0
      (by simp [Ty.width] at hSrc; omega) hBase
      (by simpa [Ty.copyScratch, Ty.scalar] using hRoom) fun heap' store' s' ptr' hStep hOwned hF
        hTop => hNext heap' store' s' [.i64 ptr'] hStep ⟨ptr', rfl, hOwned⟩ hF hTop
  | .pair a b, heap, store, s, h, src, base, mode, ws, v, rest, Q, hAt, hCap, hTrap, hh, hRep,
      hold, hSrc, hBase, hRoom, hNext => by
    obtain ⟨first, second, rfl, h1, h2, -⟩ := hRep
    have hl1 := h1.length
    obtain ⟨hold1, hold2⟩ :=
      (LocalsHold.append (hl1.trans a.types_length.symm)).mp hold
    rw [hl1] at hold2
    simp only [copyCode, List.append_assoc]
    have hScratch : ∀ c : Ty, (c = a ∨ c = b) → c.copyScratch ≤ (Ty.pair a b).copyScratch := by
      intro c hc
      unfold Ty.copyScratch
      by_cases hp : (Ty.pair a b).scalar = true
      · have := Ty.scalar_pair hp
        rcases hc with rfl | rfl <;> simp_all
      · rw [ite_eq_right hp]; split <;> omega
    refine wp_copyCode hm a hAt hCap (hTrap.within fun hw => hw.mono (Nat.le_add_right _ _)) hh
      h1 hold1 (by simp [Ty.width] at hSrc; omega) hBase
      (by have := hScratch a (Or.inl rfl); omega) fun heap1 store1 s1 ws1 hStep1 hRep1 hF1 hTop1 =>
        ?_
    have hR2 := (h2.step hStep1 fun _ _ => trivial).1
    refine wp_copyCode hm b hStep1.at_ (by rw [hStep1.cap m]; exact hCap)
      (hTrap.within fun hw => Heap.Within.after hw hTop1 (hStep1.cap m))
      (s := { s1 with values := ws1.reverse ++ s.values }) (by simp [hF1.half, hh]) hR2
      ((LocalsHold.frame (s' := { s1 with values := ws1.reverse ++ s.values })
        (hF1.trans Frame.ofValues) (h2.length.trans b.types_length.symm)
        (by rw [Ty.types_length]; simp [Ty.width] at hSrc; omega)).mpr hold2)
      (by simp [Ty.width] at hSrc; omega)
      (by show s1.params.length ≤ base; rw [hF1.params]; exact hBase)
      (by simp only [Locals.half_values, hF1.half]; have := hScratch b (Or.inr rfl); omega)
      fun heap2 store2 s2 ws2 hStep2 hRep2 hF2 hTop2 => ?_
    obtain ⟨hRep1', hSame1, hFresh1⟩ := hRep1.step hStep2 fun _ _ => trivial
    have hBlocks1 : a.blocks store2 ws1 v.1 = a.blocks store1 ws1 v.1 := hSame1
    have hStep := hStep1.transBoth (keep := fun _ => True) hStep2
      fun _ _ => ⟨trivial, fun _ => trivial⟩
    refine hNext heap2 store2 s2 (ws1 ++ ws2) ?_
      ⟨ws1, ws2, rfl, hRep1', hRep2, fun _ x hx y hy => ?_⟩
      (hF1.trans hF2.values) (by show _ ≤ _ + (a.copyCost v.1 + b.copyCost v.2); omega)
      |> fun h => by
        simpa [List.reverse_append, List.append_assoc] using h
    · rw [Ty.blocks_append hRep1.length, hBlocks1]
      exact hStep
    · rw [hBlocks1] at hx
      exact hFresh1 x hx y hy

/-- The release of the owned value of type `t` whose words locals `src` on hold: a step that
consumes the value's blocks and leaves `top`. -/
theorem wp_releaseCode {m : Module} (hm : Runtime m) {host : HostEnv Unit} :
    (t : Ty) → ∀ {heap : Heap} {store : Store Unit} {s : Locals} {src : Nat} {ws : List Value}
      {v : t.denote} {rest : Program} {Q : Assertion Unit},
    heap.At store → t.Rep .owned heap store ws v → LocalsHold s src t.types ws →
    (∀ (heap' : Heap) (store' : Store Unit),
      Step heap store (fun r => ∀ b ∈ t.blocks store ws v, regionsDisjoint r b) heap' store' [] →
      heap'.top = heap.top → wp m rest Q store' s host) →
    wp m (releaseCode t src ++ rest) Q store s host
  | .elem _, heap, store, _, _, _, _, _, _, hAt, _, _, hNext => by
    simpa [releaseCode] using hNext heap store (Step.refl hAt _) rfl
  | .array _, heap, store, s, src, ws, v, rest, Q, hAt, hRep, hold, hNext => by
    obtain ⟨ptr, rfl, hOwned⟩ := hRep
    have h0 : s.get src = some (.i64 ptr) := LocalsHold.word hold
    simp only [releaseCode, List.cons_append, List.nil_append, wp_localGet_cons, h0]
    refine wp_release hm hAt hOwned ?_
    have := hNext _ _ ((releaseStep hAt hOwned).mono (fun r hr => hr _ (List.mem_singleton_self _))
      (fun _ h => h)) rfl
    simpa using this
  | .pair a b, heap, store, s, src, ws, v, rest, Q, hAt, hRep, hold, hNext => by
    obtain ⟨first, second, rfl, h1, h2, hd⟩ := hRep
    have hl1 := h1.length
    obtain ⟨hold1, hold2⟩ :=
      (LocalsHold.append (hl1.trans a.types_length.symm)).mp hold
    rw [hl1] at hold2
    simp only [releaseCode, List.append_assoc]
    refine wp_releaseCode hm a hAt h1 hold1 fun heap1 store1 hStep1 hTop1 => ?_
    -- The second component's blocks lie apart from the first's, so the first release keeps them.
    obtain ⟨hR2, hSame2, -⟩ :=
      h2.step hStep1 fun r hr x hx => regionsDisjoint_symm (hd rfl x hx r hr)
    have hBlocks2 : b.blocks store1 second v.2 = b.blocks store second v.2 := hSame2
    refine wp_releaseCode hm b hStep1.at_ hR2 hold2 fun heap2 store2 hStep2 hTop2 => ?_
    refine hNext heap2 store2 (hStep1.trans hStep2 fun r hr => ⟨fun x hx => ?_, fun _ x hx => ?_⟩)
      (hTop2.trans hTop1)
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
        fun _ => Holds.KeepDying.transfer h0 e1.step e1.frame h10
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
in which they are no longer live, with the same `top`. -/
theorem wp_releaseVars {m : Module} (hm : Runtime m) {host : HostEnv Unit} {Γ : List Ty}
    {env : Env Γ} {slots : List Slot} {base : Nat} :
    (is : List Nat) → is.Nodup → ∀ {live : Nat → Bool} {heap : Heap} {store : Store Unit}
      {s : Locals} {rest : Program} {Q : Assertion Unit},
    Holds env slots live base heap store s → heap.At store → (∀ i ∈ is, live i = true) →
    (∀ heap' store', Evolves env slots live (fun i => live i && !is.contains i) base heap store
      s heap' store' s → heap'.top = heap.top → wp m rest Q store' s host) →
    wp m (is.flatMap (releaseVar Γ slots) ++ rest) Q store s host
  | [], _, live, heap, store, s, rest, Q, hVars, hAt, _, hNext => by
    simpa using hNext heap store (Evolves.refl hAt hVars fun i _ h => by simpa using h) rfl
  | i :: is, hNodup, live, heap, store, s, rest, Q, hVars, hAt, hLive, hNext => by
    have hi : i ∉ is := (List.nodup_cons.mp hNodup).1
    have hNodup' := (List.nodup_cons.mp hNodup).2
    let live1 := fun j => live j && j != i
    have hSub1 : ∀ j, live1 j = true → live j = true := fun j h => by
      simp only [live1, Bool.and_eq_true] at h; exact h.1
    -- The rest of the list, from the state after variable `i`.
    have hRest : ∀ heap1 store1, Evolves env slots live live1 base heap store s heap1 store1 s →
        heap1.top = heap.top →
        wp m (is.flatMap (releaseVar Γ slots) ++ rest) Q store1 s host := by
      intro heap1 store1 e1 hTop1
      refine wp_releaseVars hm is hNodup' e1.holds e1.step.at_ (fun j hj => ?_)
        fun heap2 store2 e2 hTop2 => ?_
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
        exact hNext heap2 store2 e (hTop2.trans hTop1)
    simp only [List.flatMap_cons, List.append_assoc, releaseVar]
    cases hTy : Γ[i]? with
    | none =>
      simp only
      exact hRest heap store (Evolves.refl hAt hVars fun j _ h => hSub1 j h) rfl
    | some t =>
      simp only
      let x := Var.ofIndex Γ i hTy
      have hxi : x.index = i := Var.index_ofIndex Γ i hTy
      obtain ⟨hBelow, ws, hold, hRep⟩ := hVars.get x (by rw [hxi]; exact hLive i (by simp))
      rw [hxi] at hold hRep
      by_cases hOwned : (slots.getD i default).mode = .owned
      · simp only [hOwned, ↓reduceIte]
        rw [hOwned] at hRep
        refine wp_releaseCode hm t hAt hRep hold fun heap1 store1 hStep1 hTop1 =>
          hRest heap1 store1 ?_ hTop1
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
        exact hRest heap store (Evolves.refl hAt hVars fun j _ h => hSub1 j h) rfl

/-- The release of the owned variables that `sel` selects among those live, which leaves
`top`. -/
theorem wp_releaseWhere {m : Module} (hm : Runtime m) {host : HostEnv Unit} {Γ : List Ty}
    {env : Env Γ} {slots : List Slot} {base : Nat} {sel live : Nat → Bool} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit}
    (hVars : Holds env slots live base heap store s) (hAt : heap.At store)
    (hSel : ∀ i, sel i = true → live i = true)
    (hNext : ∀ heap' store', Evolves env slots live (fun i => live i && !sel i) base heap store
      s heap' store' s → heap'.top = heap.top → wp m rest Q store' s host) :
    wp m (releaseWhere Γ slots sel ++ rest) Q store s host := by
  unfold releaseWhere
  refine wp_releaseVars hm _ (List.nodup_range.filter _) hVars hAt
    (fun i hi => hSel i (List.mem_filter.mp hi).2) fun heap' store' e hTop =>
      hNext heap' store' ?_ hTop
  have hSame : ∀ i < Γ.length,
      (((List.range Γ.length).filter sel).contains i) = sel i := by
    intro i hi
    cases h : sel i <;> simp [List.mem_filter, hi, h]
  exact ⟨e.step.mono (fun r hr => hr.congr fun i hi h1 h2 => ⟨h1, by rw [← hSame i hi]; exact h2⟩)
      (fun _ h => h), e.frame,
    e.holds.live_mono' fun i hi h => by rw [hSame i hi]; exact h⟩

end Verified
