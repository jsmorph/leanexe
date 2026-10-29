import Verified.State
import Verified.Bound
import Verified.RuntimeFacts
import Verified.TreeRelease
import Verified.ArrayCopy
import Verified.Bytes.Release
import LeanExe.Pipeline.RuntimeSpec
import LeanExe.ProofKit.ReleaseTree
import LeanExe.ProofKit.ArrayPrefix
import Verified.TreeSlotCode
import Verified.TreeHeaderCopy
import Verified.Bytes.Copy
import Verified.TreeCopyInvariant
import Verified.TreeAdvance
import Verified.TreeCopyLocals
import Verified.TreeAllocate
import Verified.LocalFrame
import Verified.TreeCopyCode
import Verified.TreeStorage
import Verified.TreeInitialize
import Verified.TreeSelect
import Verified.TreeBeginState
import Verified.TreeCopyStartInv
import Verified.TreeTestCode
import Verified.TreeCopyBufferCode
import Verified.TreeRestore
import Verified.TreeNodeLayout
import Verified.TreeCopyCompleteInv
import Verified.TreeHeaderCode
import LeanExe.TalosCompat

/-! The code that allocates, copies, and releases arrays, and its specifications: a release of an
owned array consumes its block, and a copy of a value puts each of its arrays in a new block. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

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

/-- The byte count of a block for the length `t` in local `total`, given the capacity `c` in
local `cap`: twice the capacity when that holds the length and is at most `2 ^ 32`, `2 ^ 32` when
twice the capacity holds the length and exceeds `2 ^ 32`, and the bytes that the length needs
otherwise. -/
theorem wp_requestCode {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {total cap : Nat} {t c : UInt64} {rest : Program} {Q : Assertion Unit}
    (hT : s.get total = some (.i64 t)) (hC : s.get cap = some (.i64 c))
    (ht : t.toNat < 536870912) (hc : c.toNat < 4294967296)
    (hNext : ∀ r : UInt64,
      (r.toNat = 2 * c.toNat ∧ 8 * (t.toNat + 1) ≤ 2 * c.toNat ∧ 2 * c.toNat ≤ 4294967296) ∨
        (r.toNat = 4294967296 ∧ 8 * (t.toNat + 1) ≤ 2 * c.toNat ∧ 4294967296 < 2 * c.toNat) ∨
        (r.toNat = 8 * (t.toNat + 1) ∧ 2 * c.toNat < 8 * (t.toNat + 1)) →
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
      simpa using hNext (c * 2) (Or.inl ⟨hDouble, by rw [← hDouble]; exact h1,
        by rw [← hDouble]; exact h2⟩)
    · simp (config := { decide := true }) only [h2, ↓reduceIte]
      simp only [wp_constI64_cons, wp_nil]
      rw [UInt64.le_iff_toNat_le, hNeed] at h1
      rw [UInt64.not_le, UInt64.lt_iff_toNat_lt, hDouble] at h2
      simp only [UInt64.reduceToNat] at h2
      simpa using hNext 4294967296 (Or.inr (Or.inl ⟨rfl, by rw [← hDouble]; exact h1, h2⟩))
  · simp (config := { decide := true }) only [h1, ↓reduceIte]
    simp only [wp_localGet_cons, hT, wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons, wp_nil]
    rw [UInt64.le_iff_toNat_le, hNeed, hDouble] at h1
    simpa using hNext ((t + 1) * 8) (Or.inr (Or.inr ⟨hNeed, by omega⟩))

/-- An assertion that accepts every trap at `unreachable` accepts those of any allowance. -/
theorem _root_.Wasm.TrapOK.any {b : Bool} {Q : Assertion Unit} (h : TrapOK true Q) :
    TrapOK b Q := by
  cases b
  · trivial
  · exact h

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

end Verified
