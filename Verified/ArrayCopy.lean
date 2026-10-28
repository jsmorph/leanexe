import Verified.HeapStep
import Verified.LocalFrame
import Verified.RuntimeFacts
import Verified.AllocCost
import Verified.ArrayCopyCode
import LeanExe.Pipeline.RuntimeSpec
import LeanExe.ProofKit.ArrayPrefix

/-! The specifications of the code that allocates arrays and copies them into new blocks. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The address of element `k` of the array at `ptr`. -/
theorem element_address (ptr : UInt64) (k : Nat) :
    (ptr + (UInt64.ofNat k + 1) * 8).toUInt32 = UInt64Array.wordAddress ptr (k + 1) := by
  unfold UInt64Array.wordAddress
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

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
is `n` and whose elements are what memory held, with its address in local `ptr`.
It traps at `unreachable` only when `top` cannot rise by the charge `c` within the
cap, and it raises `top` by at most `c`. -/
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
      heap'.Owned store' root words → AllocShape heap heap' bytes (capacityAt store' root) →
      heap'.top.toNat ≤ heap.top.toNat + c →
      wp m rest Q store' (setLocal { s with values := vs } ptr (.i64 root)) host) :
    wp m (allocBlockCode len ptr ++ rest) Q store { s with values := .i64 bytes :: vs } host := by
  have hn' : UInt64.ofNat n.toNat = n := UInt64.ofNat_toNat
  simp only [allocBlockCode, List.cons_append, List.nil_append]
  refine wp_alloc hm hAt hBytes32 hCap hc hTrap fun hFits hTop => ?_
  have hRound := le_allocSize hBytes32
  have hShape := Heap.allocate_shape hBytes32 hFits
  generalize hNeed : allocSize bytes = need at hFits hRound hTop hShape ⊢
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
    (by rw [hCapEq]; exact hShape) hTop

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

/-- The allocation of a block of the byte count on top of the stack for an array of `total` words,
with `total` in local `len`, and the copy into it of the array `xs`, borrowed at `ptr`, whose
address local `src` holds and whose length local `count` holds: a new owned block, with its address
in local `dst`, holding an array of `total` words whose first elements are those of `xs`.
It traps at `unreachable` only when `top` cannot rise by the charge `c` within the
cap, and it raises `top` by at most `c`. -/
theorem wp_allocCopy {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {src len count dst index : Nat} {ptr total bytes : UInt64}
    {xs : Array UInt64} {vs : List Value} {rest : Program} {Q : Assertion Unit} {c : Nat}
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hc : allocCost (allocSize bytes).toNat ≤ c)
    (hTrap : TrapOK (!decide (heap.Within store m c)) Q)
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
      AllocShape heap heap' bytes (capacityAt store' q) → s'.params = s.params →
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

/-- The copy of an array that is readable at `ptr`, whose address local `src` holds, into a new
owned array, with the locals from `base` to `base + 2` as scratch.  It traps at `unreachable` only
when `top` cannot rise by the charge `c` within the cap, and it raises `top` by at most `c`. -/
theorem wp_copyArray {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {src base : Nat} {ptr : UInt64} {xs : Array UInt64}
    {rest : Program} {Q : Assertion Unit} {c : Nat}
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hc : allocCost (8 * (xs.size + 1)) ≤ c) (hTrap : TrapOK (!decide (heap.Within store m c)) Q)
    (hB : heap.Borrowed store ptr xs) (hSrc : s.get src = some (.i64 ptr)) (hSrcBase : src < base)
    (hBase : s.params.length ≤ base) (hRoom : base + 3 ≤ s.positions)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (ptr' : UInt64),
      Step heap store (fun _ => True) heap' store' [block store' ptr'] →
      heap'.Owned store' ptr' xs → Frame base s s' → heap'.top.toNat ≤ heap.top.toNat + c →
      wp m rest Q store' { s' with values := .i64 ptr' :: s.values } host) :
    wp m (copyArrayCode src base ++ rest) Q store s host := by
  have hTot : 2 * s.positions ≤ s.params.length + s.locals.length := by
    simp only [Locals.positions]; omega
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
    refine ⟨hp2, by rw [hl2]; simp [s1, setLocal], (fun j hj => ⟨?_, ?_⟩), fun j hj => ?_⟩
    · rw [hOther2 j (by omega) (by omega)]
      show s1.get j = s.get j
      rw [Locals.get_setLocal_ne hLow1 (by omega), Locals.get_values]
    · rw [hOther2 _ (by omega) (by omega)]
      show s1.get _ = s.get _
      rw [Locals.get_setLocal_ne hLow1 (by omega), Locals.get_values]
    · rw [hOther2 _ (by omega) (by omega)]
      show s1.get _ = s.get _
      rw [Locals.get_setLocal_ne hLow1 (by omega), Locals.get_values]
  simp only [wp_localGet_cons, hQ2]
  have hv1 : s1.values = s.values := rfl
  simpa [hv2, hv1] using hNext heap1 store1 s2 q hStep hOwned hF hTop

end Verified
