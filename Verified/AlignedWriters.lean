import Verified.AlignedLoops

/-!
The array writers under the flag: `build`, `set`, `push`, `append`, `insertAt`, `eraseAt`, and the
room they share.  Every word that their code loads or stores lies in an array whose pointer is a
multiple of 8: an owned variable's, which `HoldsA` covers, or a new block's, which the flagged
allocation gives.  The lemmas about code are their originals in `After.lean` and `Heap.lean` with
`wpX strict` for `wp`, a premise that the array's pointer is a multiple of 8, and the alignment
conjunct of each access; `wpX_requestCode` carries `wp_requestCode`, whose code is free of
64-bit accesses.  A write inside an owned block keeps the block, so the variable's alignment
persists across it by `Ty.AlignedVal.step`.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

section

variable {m : Module}

theorem wpX_toWordCode {strict : Bool} {st : Store Unit} {env' : HostEnv Unit} {s : Locals}
    {vs : List Value} {rest : Program} {Q : Assertion Unit} (ty : ValueType) (w : UInt64) :
    wpX strict m (toWordCode ty ++ rest) Q st { s with values := typedValue ty w :: vs } env' ↔
      wpX strict m rest Q st { s with values := .i64 (Value.word (typedValue ty w)) :: vs }
        env' := by
  cases ty <;> simp [toWordCode, typedValue, Value.word]
  rw [UInt64.ofNat_mod w.toNat_lt (by decide), UInt64.ofNat_toNat]
  rfl

theorem wp_toWordCode {m : Module} {st : Store Unit} {env' : HostEnv Unit} {s : Locals}
    {vs : List Value} {rest : Program} {Q : Assertion Unit} (ty : ValueType) (w : UInt64) :
    wp m (toWordCode ty ++ rest) Q st { s with values := typedValue ty w :: vs } env' ↔
      wp m rest Q st { s with values := .i64 (Value.word (typedValue ty w)) :: vs } env' :=
  wpX_toWordCode (strict := false) ty w

/-- The writes of the words of types `tys` at positions `src` on as the words `w + j` on of an
owned array value at `p`: the array with those words replaced, in the same block.  `w` is the word
in local `w0`. -/
theorem wpX_storeWordsCode {strict : Bool} {m : Module} {host : HostEnv Unit} {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 : Heap} {store0 : Store Unit} {s0 : Locals} {h ptr w0 : Nat}
    {p w : UInt64} {rest : Program} {Q : Assertion Unit}
    (hpAl : strict = true → p.toNat % 8 = 0) :
    (j src : Nat) → (tys : List ValueType) → (words : List UInt64) → (ws : Array UInt64) →
    (store1 : Store Unit) → (s : Locals) →
    After env slots L0 L base heap store0 s0 (.array .word) .owned ws heap1 store1 s [.i64 p] →
    s.positions = h → s.get ptr = some (.i64 p) → s.get w0 = some (.i64 w) →
    LocalsHold s src tys (List.zipWith typedValue tys words) → words.length = tys.length →
    (List.zipWith typedValue tys words).map Value.word = words →
    w.toNat + j + tys.length ≤ ws.size →
    (∀ store2, After env slots L0 L base heap store0 s0 (.array .word) .owned
        (writeWords ws (w.toNat + j) words) heap1 store2 s [.i64 p] →
      capacityAt store2 p = capacityAt store1 p → wpX strict m rest Q store2 s host) →
    wpX strict m (storeWordsCode h ptr w0 j src tys ++ rest) Q store1 s host
  | _, _, [], words, ws, store1, s, a, _, _, _, _, hl, _, _, hk => by
    obtain rfl : words = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simpa [storeWordsCode, writeWords] using hk store1 a rfl
  | j, src, ty :: tys, v :: words, ws, store1, s, a, hh, hP, hW, hold, hl, normal, hFit, hk => by
    have normal' : Value.word (typedValue ty v) = v ∧
        (List.zipWith typedValue tys words).map Value.word = words := by
      simpa only [List.zipWith_cons_cons, List.map_cons, List.cons.injEq] using normal
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.length_cons] at hFit
    have hn : w.toNat + j < ws.size := by omega
    obtain ⟨q, hq, hOwned⟩ := a.rep
    replace hOwned : heap1.Owned store1 q ws := hOwned
    obtain rfl : q = p := by simp only [List.cons.injEq, Value.i64.injEq] at hq; exact hq.1.symm
    have hA := hOwned.values
    have hOffset := word_offset hn (by have := hA.1; omega)
    have hElement := hA.elementBound _ hn
    have hv : s.get (slotIndex h src ty) = some (typedValue ty v) := by
      have := hold 0 (by simp)
      simpa [hh, List.zipWith_cons_cons] using this
    have holdRest : LocalsHold s (src + 1) tys (List.zipWith typedValue tys words) := by
      intro k hk'
      have := hold (k + 1) (by simp only [List.zipWith_cons_cons, List.length_cons]; omega)
      simpa [List.zipWith_cons_cons, Nat.add_assoc, Nat.add_comm 1 k] using this
    simp only [storeWordsCode, wordAddrCode, List.append_assoc, List.cons_append,
      List.nil_append, wpX_localGet_cons, Locals.get_values, hP, hW, wpX_constI64_cons,
      wpX_addI64_cons, wpX_mulI64_cons, wpX_wrapI64_cons, wrap_toUInt32, hOffset, hv]
    rw [wpX_toWordCode, normal'.1]
    simp only [wpX_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by omega)]
    refine ⟨fun hs => elementAddress_mod8 (hpAl hs) (w.toNat + j), ?_⟩
    refine wpX_storeWordsCode hpAl (j + 1) (src + 1) tys words _ _ s (a.writeElement hn v) hh hP hW
      holdRest hl normal'.2 (by rw [Array.size_set]; omega) fun store2 a2 hc =>
        hk store2 ?_ (hc.trans (capacityAt_writeElement hOwned hn v))
    have hSet : ws.set (w.toNat + j) v hn = ws.set! (w.toNat + j) v := by
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hn]
    rw [hSet, show w.toNat + (j + 1) = w.toNat + j + 1 by omega] at a2
    exact a2

/-- The writes of the words of types `tys` at positions `src` on as the words `w + j` on of an
owned array value at `p`: the array with those words replaced, in the same block.  `w` is the word
in local `w0`. -/
theorem wp_storeWordsCode {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 : Heap} {store0 : Store Unit} {s0 : Locals} {h ptr w0 : Nat}
    {p w : UInt64} {rest : Program} {Q : Assertion Unit} :
    (j src : Nat) → (tys : List ValueType) → (words : List UInt64) → (ws : Array UInt64) →
    (store1 : Store Unit) → (s : Locals) →
    After env slots L0 L base heap store0 s0 (.array .word) .owned ws heap1 store1 s [.i64 p] →
    s.positions = h → s.get ptr = some (.i64 p) → s.get w0 = some (.i64 w) →
    LocalsHold s src tys (List.zipWith typedValue tys words) → words.length = tys.length →
    (List.zipWith typedValue tys words).map Value.word = words →
    w.toNat + j + tys.length ≤ ws.size →
    (∀ store2, After env slots L0 L base heap store0 s0 (.array .word) .owned
        (writeWords ws (w.toNat + j) words) heap1 store2 s [.i64 p] →
      capacityAt store2 p = capacityAt store1 p → wp m rest Q store2 s host) →
    wp m (storeWordsCode h ptr w0 j src tys ++ rest) Q store1 s host :=
  wpX_storeWordsCode (strict := false) nofun

/-- The loop of `shiftUpCode`: in the array `ws` at `p`, whose address local `ptr` holds, the words
from position `l`, in local `lo`, to position `h`, in local `index`, move up by `k`.  The loop
writes only inside the region of `ws` and changes no local but `index`. -/
theorem wpX_shiftUp {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {ptr lo index k : Nat} {p : UInt64} {ws : Array UInt64} {l h : Nat}
    {rest : Program} {Q : Assertion Unit}
    (hA : UInt64Array.At store p ws)
    (hpAl : strict = true → p.toNat % 8 = 0) (hlh : l ≤ h) (hFit : h + k ≤ ws.size)
    (hP : s.get ptr = some (.i64 p)) (hLo : s.get lo = some (.i64 (UInt64.ofNat l)))
    (hIdx : s.get index = some (.i64 (UInt64.ofNat h)))
    (hPI : ptr ≠ index) (hLI : lo ≠ index)
    (hLow : s.params.length ≤ index) (hHigh : index < s.params.length + s.locals.length)
    (hNext : ∀ (store' : Store Unit) (s' : Locals),
      Memory.WritesRange store store' p.toNat (p.toNat + 8 * (ws.size + 1)) →
      UInt64Array.At store' p (shiftUp ws l h k) →
      s'.params = s.params → s'.locals.length = s.locals.length →
      (∀ j, j ≠ index → s'.get j = s.get j) → s'.values = s.values →
      wpX strict m rest Q store' s' host) :
    wpX strict m (shiftUpCode ptr lo index k ++ rest) Q store s host := by
  have hFitA := hA.1
  have hl64 : (UInt64.ofNat l).toNat = l :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  simp only [shiftUpCode, List.cons_append, List.nil_append]
  refine wpX_block_cons ?_
  refine wpX_loop_cons
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
  simp only [wpX_localGet_cons, Locals.get_values, hT, hOther lo hLI, hLo, wpX_leUI64_cons,
    wpX_br_if_cons]
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
    simp only [wpX_constI64_cons, wpX_subI64_cons, hPred]
    have hLowI : si.params.length ≤ index := by rw [hp]; exact hLow
    have hHighI : index < si.params.length + si.locals.length := by rw [hp, hl]; exact hHigh
    refine wpX_localSet_local (s := si) (vs := si.values) hLowI hHighI ?_
    have hLowI' : ({ si with values := si.values } : Locals).params.length ≤ index := hLowI
    have hGetI := Locals.get_setLocal_same hLowI' hHighI (v := .i64 (UInt64.ofNat (t - 1)))
    have hGetP : (setLocal { si with values := si.values } index
        (.i64 (UInt64.ofNat (t - 1)))).get ptr = some (.i64 p) := by
      rw [Locals.get_setLocal_ne hLowI' hPI, Locals.get_values, hOther ptr hPI, hP]
    have hRd : t - 1 < (shiftUp ws t h k).size := by rw [shiftUp_size]; omega
    have hWr : t - 1 + k < (shiftUp ws t h k).size := by rw [shiftUp_size]; omega
    have hSrcElement := hAt.elementBound (t - 1) hRd
    have hDstElement := hAt.elementBound (t - 1 + k) hWr
    simp only [wpX_localGet_cons, Locals.get_values, hGetP, hGetI, wpX_constI64_cons,
      wpX_addI64_cons, wpX_mulI64_cons, wpX_wrapI64_cons, wrap_toUInt32, element_address_up,
      element_address]
    simp only [wpX_load64_cons, wpX_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
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
    refine ⟨fun hs => wordAddress_mod8 (hpAl hs) _, fun hs => wordAddress_mod8 (hpAl hs) _, ?_⟩
    rw [wpX_br_cons]
    dsimp only
    refine ⟨⟨t - 1, by omega, by omega, hW.trans (UInt64Array.writeElement_frame st p ws.size
      (t - 1 + k) ws[t - 1]! hFitA (by omega)), ?_, hp, by simp [setLocal, hl], fun j hj => ?_,
      by rw [Locals.get_values]; exact hGetI⟩, ?_⟩
    · rw [← shiftUp_step (by omega) hFit hth]
      exact hAt.writeElement hWr ws[t - 1]!
    · rw [Locals.get_values, Locals.get_setLocal_ne hLowI' hj, Locals.get_values]
      exact hOther j hj
    · simp only [hGetI, ht64]
      rw [UInt64.toNat_ofNat_of_lt'
        (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
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
    wp m (shiftUpCode ptr lo index k ++ rest) Q store s host :=
  wpX_shiftUp (strict := false) hA nofun hlh hFit hP hLo hIdx hPI hLI hLow hHigh hNext

/-- The loop of `copyIntoCode` inside one array: in the array `ws` at `p`, the `n` words from
position `l + k` on move down by `k`, with `p + 8 (l + k)` in local `src` and `p + 8 l` in local
`dst`.  Each word is read before the loop writes it, since the writes trail the reads.  The loop
writes only inside the region of `ws` and changes no local but `index`. -/
theorem wpX_copyDown {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {src dst count index : Nat} {p : UInt64} {ws : Array UInt64} {l n k : Nat}
    {rest : Program} {Q : Assertion Unit}
    (hA : UInt64Array.At store p ws)
    (hpAl : strict = true → p.toNat % 8 = 0) (hFit : l + n + k ≤ ws.size)
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
      wpX strict m rest Q store' s' host) :
    wpX strict m (copyIntoCode src dst count index ++ rest) Q store s host := by
  have hFitA := hA.1
  simp only [copyIntoCode, List.cons_append, List.nil_append, wpX_constI64_cons]
  refine wpX_localSet_local (s := s) (vs := s.values) hLow hHigh ?_
  have hLow0 : ({ s with values := s.values } : Locals).params.length ≤ index := hLow
  refine wpX_block_cons ?_
  refine wpX_loop_cons
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
  simp only [wpX_localGet_cons, Locals.get_values, hIdx, hOther count hCountI, hCount,
    wpX_geUI64_cons, wpX_br_if_cons]
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
    simp only [wpX_localGet_cons, Locals.get_values, hOther dst hDstI, hDst, hIdx,
      hOther src hSrcI, hSrc, wpX_constI64_cons, wpX_addI64_cons, wpX_mulI64_cons, wpX_wrapI64_cons,
      wrap_toUInt32, element_address_at]
    simp only [wpX_load64_cons, wpX_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
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
    refine ⟨fun hs => wordAddress_mod8 (hpAl hs) _, fun hs => wordAddress_mod8 (hpAl hs) _, ?_⟩
    simp only [wpX_localGet_cons, hIdx, wpX_constI64_cons, wpX_addI64_cons]
    have hLowI : si.params.length ≤ index := by rw [hp]; exact hLow
    have hHighI : index < si.params.length + si.locals.length := by rw [hp, hl]; exact hHigh
    refine wpX_localSet_local (s := si) (vs := si.values) hLowI hHighI ?_
    rw [wpX_br_cons]
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
    wp m (copyIntoCode src dst count index ++ rest) Q store s host :=
  wpX_copyDown (strict := false) hA nofun hFit hSrc hDst hCount hSrcI hDstI hCountI hLow hHigh hNext

/-- `wp_allocArray` under the flag. -/
theorem wpX_allocArray {strict : Bool} (hm : Runtime m) (hRt : strict = true → AllocAligned m)
    {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {count ptr : Nat} {n : UInt64} {rest : Program}
    {Q : Assertion Unit} {c : Nat} (hAt : heap.At store) (hHeapAl : strict = true → heap.Aligned)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hc : allocCost (8 * (n.toNat + 1)) ≤ c) (hTrap : TrapOK (!decide (heap.Within store m c)) Q)
    (hn : n.toNat < 536870912) (hN : s.get count = some (.i64 n))
    (hLow : s.params.length ≤ ptr) (hHigh : ptr < s.params.length + s.locals.length)
    (hne : count ≠ ptr)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (root : UInt64) (words : Array UInt64),
      words.size = n.toNat → Step heap store (fun _ => True) heap' store' [block store' root] →
      heap'.Owned store' root words → heap'.top.toNat ≤ heap.top.toNat + c →
      (strict = true → root.toNat % 8 = 0 ∧ capacityAt store' root % 8 = 0 ∧ heap'.Aligned) →
      wpX strict m rest Q store' (setLocal { s with values := s.values } ptr (.i64 root)) host) :
    wpX strict m (allocArrayCode count ptr ++ rest) Q store s host := by
  have hn' : UInt64.ofNat n.toNat = n := UInt64.ofNat_toNat
  obtain ⟨hBytes, hSize⟩ := allocSize_words hn
  rw [hn'] at hBytes hSize
  simp only [allocArrayCode, List.cons_append, List.nil_append, wpX_localGet_cons, hN,
    wpX_constI64_cons, wpX_addI64_cons, wpX_mulI64_cons]
  exact wpX_allocBlock hm hRt hAt hHeapAl hCap (by rw [hSize, hBytes]; exact hc) hTrap hn
    (by rw [hBytes]) (by rw [hBytes]; omega) hN hLow hHigh hne
    fun heap' store' root words hSize hStep hOwned _ hTop hAl =>
      hNext heap' store' root words hSize hStep hOwned hTop hAl

/-- The allocation of an array of `n` words, with `n` in local `count`: a new owned block whose
length word is `n` and whose elements are what memory held, with its address in local `ptr`.
It traps at `unreachable` only when `top` cannot rise by the charge `c` within the
cap, and it raises `top` by at most `c`. -/
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
    wp m (allocArrayCode count ptr ++ rest) Q store s host :=
  wpX_allocArray (strict := false) hm nofun hAt nofun hCap hc hTrap hn hN hLow hHigh hne
    (fun heap' store' root words a1 a2 a3 a4 _ => hNext heap' store' root words a1 a2 a3 a4)

theorem requestCode_free (total cap : Nat) : freeCode (requestCode total cap) = true := rfl

/-- `wp_requestCode` under the flag. -/
theorem wpX_requestCode {strict : Bool} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {total cap : Nat} {t c : UInt64} {rest : Program} {Q : Assertion Unit}
    (hT : s.get total = some (.i64 t)) (hC : s.get cap = some (.i64 c))
    (ht : t.toNat < 536870912) (hc : c.toNat < 4294967296)
    (hNext : ∀ r : UInt64,
      (r.toNat = 2 * c.toNat ∧ 8 * (t.toNat + 1) ≤ 2 * c.toNat ∧ 2 * c.toNat ≤ 4294967296) ∨
        (r.toNat = 4294967296 ∧ 8 * (t.toNat + 1) ≤ 2 * c.toNat ∧ 4294967296 < 2 * c.toNat) ∨
        (r.toNat = 8 * (t.toNat + 1) ∧ 2 * c.toNat < 8 * (t.toNat + 1)) →
      wpX strict m rest Q store { s with values := .i64 r :: s.values } host) :
    wpX strict m (requestCode total cap ++ rest) Q store s host := by
  refine wpX_append_free (requestCode_free total cap) ?_
  have := wp_requestCode (m := m) (host := host) (rest := []) (Q := ThenX strict m rest Q host)
    hT hC ht hc fun r hr => wp_nil.mpr (hNext r hr)
  rwa [List.append_nil] at this

end

section

variable {Γ : List Ty} {env : Env Γ} {slots : List Slot}

/-- The invariant after an expression's code: the variables live after it keep their regions
across its step, so their alignment persists, given an aligned heap at its end. -/
theorem HoldsA.after {L0 L : Nat → Bool} {base : Nat} {heap heap' : Heap}
    {store store' : Store Unit} {s s' : Locals} {t : Ty} {mode : Mode} {v : t.denote}
    {ws : List Value} (h0 : Holds env slots L0 base heap store s)
    (hA : HoldsA env slots L0 heap store s)
    (a : After env slots L0 L base heap store s t mode v heap' store' s' ws)
    (hL : ∀ i, L i = true → L0 i = true) (hAl : heap'.Aligned) :
    HoldsA env slots L heap' store' s' := by
  refine ⟨hAl, fun u y hy wy hwy hly => ?_⟩
  have hwy0 := (h0.hold_agree a.frame (hL _ hy) hly).mp hwy
  obtain ⟨_, wy', hold', hRep⟩ := h0.1 u y (hL _ hy)
  obtain rfl := LocalsHold.unique hwy0 hold' (hly.trans hRep.length.symm)
  exact (hA.2 u y (hL _ hy) wy hwy0 hly).step a.step hRep (h0.keepDying hL hy hwy0 hly)

/-- `After.alignedSeq` for a second value whose code starts from the first's locals. -/
theorem After.alignedSeq' {L0 L1 live : Nat → Bool} {base : Nat} {heap heap1 heap2 : Heap}
    {store store1 store2 : Store Unit} {s s1 s2 : Locals} {t u : Ty} {m1 m2 : Mode}
    {v1 : t.denote} {v2 : u.denote} {ws1 ws2 : List Value}
    (a1 : After env slots L0 L1 base heap store s t m1 v1 heap1 store1 s1 ws1)
    (a2 : After env slots L1 live base heap1 store1 s1 u m2 v2 heap2 store2 s2 ws2)
    (h : Ty.AlignedVal m1 store1 t ws1 v1) : Ty.AlignedVal m1 store2 t ws1 v1 :=
  After.alignedSeq (vs := s1.values) a1 a2 h

end

/-- The capacity of an object whose header lies below a range of writes is unchanged. -/
theorem capacity_writesRange {store store' : Store Unit} {p : UInt64} {hi : Nat}
    (hBase : 48 ≤ p.toNat) (hFit : p.toNat < 4294967296)
    (hW : Memory.WritesRange store store' p.toNat hi) : capacityAt store' p = capacityAt store p :=
  capacityAt_frame hBase hFit fun a _ h2 => hW.2.2 a (by omega)

/-- An owned array whose pointer and capacity are multiples of 8 is aligned. -/
theorem Ty.AlignedVal.ownedArray {store : Store Unit} {e : Elem} {p : UInt64}
    {xs : Array e.denote} (hp : p.toNat % 8 = 0) (hc : capacityAt store p % 8 = 0) :
    Ty.AlignedVal .owned store (.array e) [.i64 p] xs := by
  intro r hr
  simp only [Ty.regions, Ty.blocks, List.mem_singleton] at hr
  subst hr
  simp only [block]
  exact ⟨by omega, fun _ => by omega⟩

/-- The pointer of an aligned owned array, above the first header, is a multiple of 8. -/
theorem Ty.AlignedVal.ownedPtr {store : Store Unit} {e : Elem} {p : UInt64}
    {xs : Array e.denote} (hb : 48 ≤ p.toNat)
    (h : Ty.AlignedVal .owned store (.array e) [.i64 p] xs) : p.toNat % 8 = 0 := by
  have := (h (block store p) (by simp [Ty.regions, Ty.blocks])).1
  simp only [block] at this
  omega

/-- The capacity of an aligned owned array is a multiple of 8. -/
theorem Ty.AlignedVal.arrayCap {store : Store Unit} {e : Elem} {p : UInt64}
    {xs : Array e.denote} (h : Ty.AlignedVal .owned store (.array e) [.i64 p] xs) :
    capacityAt store p % 8 = 0 := by
  have := (h (block store p) (by simp [Ty.regions, Ty.blocks])).2 rfl
  simp only [block] at this
  omega

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit} {pv : List Value} {strict : Bool}

/-- `spec_ownedVar` under the flag. -/
theorem specX_ownedVar (hCopy : CopyCodeX strict m host) {Γ' : List Ty} {tTy : Ty}
    (x : Var Γ' tTy)
    {env : Env Γ'} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit} (hh : s.positions = h)
    (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || i == x.index) base heap store s)
    (hAt : heap.At store)
    (hAl : strict = true → HoldsA env slots (fun i => live i || i == x.index) heap store s)
    (hSafe : pool.Safe env slots (fun i => live i || i == x.index) heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoom : base + copyWidth tTy ≤ h)
    (hTrap : TrapOK (!decide (heap.Within store m
      (x.ownedCost (slots.map Slot.mode) live (env.get x)))) Q)
    (hNext : ∀ heap' store' s' ws,
      After env slots (fun i => live i || i == x.index) live base heap store s tTy .owned
        (env.get x) heap' store' s' ws →
      (strict = true → HoldsA env slots live heap' store' s' ∧
        Ty.AlignedVal .owned store' tTy ws (env.get x)) →
      heap'.top.toNat ≤ heap.top.toNat + x.ownedCost (slots.map Slot.mode) live (env.get x) →
      wpX strict m rest Q store' { s' with values := ws.reverse ++ s.values } host) :
    wpX strict m (x.ownedCode h slots base live ++ rest) Q store s host := by
  simp only [Var.ownedCode, List.append_assoc]
  have hScratch := tTy.copyScratch_le
  have hMode : modeAt (slots.map Slot.mode) x.index = (slots.getD x.index default).mode :=
    Slot.modes_getD slots x.index
  refine specX_var (S := []) (funs := .nil) (flags := .nil) (bounds := .nil) (fits := .nil)
      (pool := pool) hCopy x env slots [] live h
      base heap store s hh hpv hVars hAt hAl
    hSafe hCap hBase (by simp only [Expr.width]; omega) rfl _ _
    (hTrap.narrow fun hw => hw.mono (by
      rw [dyingPot_nil]; simp only [Expr.allocs, Var.ownedCost]; omega))
    fun heap1 store1 s1 ws1 a1 hAl1 hTop1 => ?_
  have hTop1' := hTop1 rfl
  simp only [Expr.allocs, Expr.paid, paidAt, List.getD_nil, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte, Nat.add_zero, dyingPot_nil] at hTop1'
  rw [show (Expr.var (S := []) x).mode (slots.map Slot.mode) = (slots.getD x.index default).mode
    from Slot.modes_getD slots x.index] at a1 hAl1
  exact After.coerceX hCopy a1 hAl1 (fun _ => rfl) le_rfl (by rw [a1.frame.params]; exact hBase)
    (a1.frame.positions.trans hh) (by omega) (by rw [a1.step.cap m]; exact hCap)
    (fun hs _ _ => hTrap.within fun hw => by
      have h2 := hw.after (heap1 := heap1) (store1 := store1)
        (c1 := x.cost (slots.map Slot.mode) live (env.get x))
        (c2 := coerceCost tTy (modeAt (slots.map Slot.mode) x.index) .owned (env.get x)) hTop1'
        (a1.step.cap m)
      simp only [coerceCost, hMode, hs, and_self, ↓reduceIte] at h2
      exact h2)
    fun heap2 store2 s2 ws2 a2 hTop2 _ hAl2 => hNext heap2 store2 s2 ws2 a2 hAl2 (by
      simp only [Expr.denote] at hTop2
      simp only [Var.ownedCost]; rw [hMode]; omega)

/-- `LeanExe.build`: the count in local `base`, a trap at `unreachable` when it is `2 ^ 29` or
more, a new owned array at the address in local `base + 1`, and the index in local `base + 2`.
The invariant at the top of the WebAssembly `loop` holds an owned array of the count's length
whose elements below the index are the built ones, with the facts of `After` for the outer
variables live in the loop.  Each iteration runs the element's code in the context with the
index, which keeps every region, and stores the element. -/
theorem specX_build (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (hRt : strict = true → AllocAligned m) {Γ' : List Ty} {e : Elem} {count : Expr S Γ' .word}
    {elem : Expr S (.word :: Γ') (.elem e)}
    (countSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv count env
        slots paid live)
    (elemSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv elem env
        slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.build count elem) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc := Nat.le_max_left count.width (3 + max elem.width (e.width + 1))
  have he := Nat.le_max_right count.width (3 + max elem.width (e.width + 1))
  have he1 := Nat.le_max_left elem.width (e.width + 1)
  have he2 := Nat.le_max_right elem.width (e.width + 1)
  have hk := e.width_pos
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  have hT : (Expr.build count elem).allocs funs flags bounds (slots.map Slot.mode) paid live env =
      count.allocs funs flags bounds (slots.map Slot.mode) paid
          (fun i => live i || elem.uses (i + 1)) env +
        allocCost (((count.denote funs env).toNat * e.width + 1) * 8) +
        sumBelow
            (fun k => elem.allocs funs flags bounds (.borrowed :: slots.map Slot.mode) (false :: paid)
          (shift 1 (fun i => live i || elem.uses (i + 1))) (.cons (UInt64.ofNat k) env))
          (count.denote funs env).toNat := rfl
  have hdK : (Expr.build count elem).fits funs fits env = true → count.fits funs fits env = true ∧
      ∀ k, k < (count.denote funs env).toNat →
        elem.fits funs fits (.cons (UInt64.ofNat k) env) = true := fun hd => by
    simp only [Expr.fits, Bool.and_eq_true] at hd
    exact ⟨hd.1, allBelow_get hd.2⟩
  have hTrapW : ¬heap.Within store m
      (dyingPot store s env slots paid (fun i => live i || (Expr.build count elem).uses i) live +
        (Expr.build count elem).allocs funs flags bounds (slots.map Slot.mode) paid live env) →
      TrapOK true Q := fun hw =>
    hTrap.of_imp fun _ => by simp [trapFlag, Expr.aborts, hw]
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc, List.cons_append, List.nil_append]
  -- The count, in local `base`.
  have hCountIn : ∀ i, ((live i || elem.uses (i + 1)) || count.uses i) = true →
      (live i || (Expr.build count elem).uses i) = true := fun i h => by
    simp only [Expr.uses]; exact live_seq _ _ _ h
  -- The variables that die in the count.  The others that die in the build are released after
  -- it, and their potential is dropped.
  have hDk : dyingPot store s env slots paid
      (fun i => (live i || elem.uses (i + 1)) || count.uses i)
      (fun i => live i || elem.uses (i + 1)) ≤
        dyingPot store s env slots paid (fun i => live i || (Expr.build count elem).uses i) live :=
    dyingPot_mono hCountIn fun i h => by simp [h]
  -- No paid variable dies in an element: the index is unpaid, and the outer variables that the
  -- element uses stay live.
  have hDe : ∀ (v : UInt64) (st' : Store Unit) (s' : Locals) (sl : Slot),
      dyingPot st' s' (Env.cons (t := .word) v env) (sl :: slots) (false :: paid)
        (fun j => shift 1 (fun i => live i || elem.uses (i + 1)) j || elem.uses j)
        (shift 1 fun i => live i || elem.uses (i + 1)) = 0 := fun _ _ _ _ =>
    dyingPot_eq_zero_unpaid fun j h0 h1 => by
      match j with
      | 0 => rfl
      | k + 1 =>
        have hk : ¬ k + 1 < 1 := by omega
        simp only [shift, hk, ↓reduceIte, Nat.add_sub_cancel] at h0 h1
        revert h0 h1
        cases live k <;> cases elem.uses (k + 1) <;> simp
  refine countSpec env slots paid _ h base heap store s hh hpv
    (hVars.live_mono hCountIn) hAt (fun hs => (hAl hs).live_mono hCountIn)
    (hSafe.mono hCountIn) hCap hBase (by omega) hPlace.1 _ _
    (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun _ => by simp [Expr.aborts]) fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hAlK hTopK => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.positions = h := e1.frame.positions.trans hh
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; exact hBase
  have hHigh1 : base < s1.positions := by rw [hh1]; omega
  refine wpX_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  set s2 := setLocal { s1 with values := s.values } base (.i64 (count.denote funs env)) with hs2
  have f2 : Frame base s1 s2 := Frame.setValues hLow1 le_rfl hHigh1
  have hN2 : s2.get base = some (.i64 (count.denote funs env)) :=
    Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1)
  have hh2 : s2.positions = h := by simp only [hs2, Locals.positions_setLocal, Locals.positions_values, hh1]
  -- The trap when the count's words would be `2 ^ 29` or more.
  simp only [wpX_localGet_cons, hN2, wpX_constI64_cons, wpX_geUI64_cons]
  refine wpX_iff_cons rfl ?_
  by_cases hBig : UInt64.ofNat ((536870912 + e.width - 1) / e.width) ≤ count.denote funs env
  · simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
    rw [wpX_unreachable_cons]
    refine hTrapW (fun hw => ?_) _
    have hLim' : (536870912 + e.width - 1) / e.width < UInt64.size := by
      rw [show UInt64.size = 18446744073709551616 from rfl]
      have hd : (536870912 + e.width - 1) / e.width ≤ 536870912 :=
        Nat.div_le_of_le_mul (by omega)
      omega
    have hge := UInt64.le_iff_toNat_le.mp hBig
    rw [UInt64.toNat_ofNat_of_lt' hLim'] at hge
    have hlt := Nat.lt_mul_div_succ (536870912 + e.width - 1) hk
    have hmul := Nat.mul_le_mul_right e.width hge
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm] at hlt
    unfold Heap.Within at hw
    rw [hT] at hw
    unfold allocCost at hw
    omega
  simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
  rw [wpX_nil]
  dsimp only
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  have hLim : (536870912 + e.width - 1) / e.width < UInt64.size := by
    rw [show UInt64.size = 18446744073709551616 from rfl]
    have hd : (536870912 + e.width - 1) / e.width ≤ 536870912 :=
      Nat.div_le_of_le_mul (by omega)
    omega
  have hcLim : (count.denote funs env).toNat < (536870912 + e.width - 1) / e.width := by
    have := UInt64.not_le.mp hBig
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hLim] at this
    exact this
  have hck := build_limit hk hcLim
  have hcSmall : (count.denote funs env).toNat ≤ (count.denote funs env).toNat * e.width :=
    Nat.le_mul_of_pos_right _ hk
  -- The count of words, in local `base + 2`.
  show wpX strict m _ Q store1 s2 host
  simp only [wpX_localGet_cons, hN2]
  rw [wpX_scaleCode, show count.denote funs env = UInt64.ofNat (count.denote funs env).toNat by simp,
    words_scale hk hck]
  have hLowT : ({ s2 with values := s.values } : Locals).params.length ≤ base + 2 := by
    show s1.params.length ≤ base + 2; rw [hp1]; omega
  have hHighT : base + 2 < ({ s2 with values := s.values } : Locals).positions := by
    simp only [Locals.positions_values, hh2]; omega
  refine wpX_localSet_local hLowT (Locals.lt_total hHighT) ?_
  set s3 := setLocal { s2 with values := s.values } (base + 2)
    (.i64 (UInt64.ofNat ((count.denote funs env).toNat * e.width))) with hs3
  have hT3 : s3.get (base + 2) =
      some (.i64 (UInt64.ofNat ((count.denote funs env).toNat * e.width))) :=
    Locals.get_setLocal_same hLowT (Locals.lt_total hHighT)
  have hN3 : s3.get base = some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLowT (by omega), Locals.get_values]; exact hN2
  have f3 : Frame base s2 s3 := Frame.setValues hLowT (by omega) (by simpa using hHighT)
  have hh3 : s3.positions = h := by simp only [hs3, Locals.positions_setLocal, Locals.positions_values, hh2]
  have hp3 : s3.params = s.params := by
    simp only [hs3, hs2, setLocal]; exact hp1
  -- The new array, at the address in local `base + 1`.
  have hTn : (UInt64.ofNat ((count.denote funs env).toNat * e.width)).toNat =
      (count.denote funs env).toNat * e.width :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hLow4 : s3.params.length ≤ base + 1 := by rw [hp3]; omega
  have hHigh4' : base + 1 < s3.positions := by rw [hh3]; omega
  have hHigh4 := Locals.lt_total hHigh4'
  refine wpX_allocArray (c := allocCost (((count.denote funs env).toNat * e.width + 1) * 8)) hm hRt
    e1.step.at_ (fun hs => (hAlK hs).1.1) (by rw [e1.step.cap m]; exact hCap)
    (by rw [hTn]; unfold allocCost; omega)
    (hTrap.alloc (by simp [Expr.aborts]) fun hd hw => by
      have := hTopK (hdK (fits_of_not hd)).1
      exact hw.shift (c1 := dyingPot store s env slots paid
          (fun i => (live i || elem.uses (i + 1)) || count.uses i)
          (fun i => live i || elem.uses (i + 1)) +
          count.allocs funs flags bounds (slots.map Slot.mode) paid (fun i => live i || elem.uses (i + 1))
            env)
        (by omega) (by rw [hT]; omega) (e1.step.cap m))
    (by rw [hTn]; exact hck) hT3 hLow4 hHigh4 (by omega)
    fun heap2 store2 root words hSize hStepA hOwned hTopA hAlA => ?_
  have hRootAl : strict = true → root.toNat % 8 = 0 := fun hs => (hAlA hs).1
  rw [hTn] at hSize
  set s4 := setLocal { s3 with values := s3.values } (base + 1) (.i64 root) with hs4
  have f4 : Frame base s3 s4 := Frame.setValues hLow4 (by omega) hHigh4'
  have hF4 : Frame base s s4 := e1.frame.trans (f2.trans (f3.trans f4))
  have hN4 : s4.get base = some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]; exact hN3
  have hRoot4 : s4.get (base + 1) = some (.i64 root) := Locals.get_setLocal_same hLow4 hHigh4
  have hh4 : s4.positions = h := by simp only [hs4, Locals.positions_setLocal, hh3]
  have hp4 : s4.params = s.params := by simp only [hs4, setLocal]; exact hp3
  -- The facts of `After` for the new array.
  have hVars1 : Holds env slots (fun i => live i || elem.uses (i + 1)) base heap1 store1 s4 :=
    e1.holds.agree (f2.trans (f3.trans f4))
  have a0 : After env slots (fun i => live i || (Expr.build count elem).uses i)
      (fun i => live i || elem.uses (i + 1)) base heap store s (.array .word) .owned words heap2
      store2 s4 [.i64 root] := by
    refine ⟨(e1.step.trans hStepA fun _ hr => ⟨hr, fun _ => trivial⟩).mono
      (fun _ hr => hr.mono fun i h1 h2 => ⟨hCountIn i h1, h2⟩) (fun _ h => h), hF4,
      hVars1.step hStepA (fun _ _ _ _ _ _ _ _ => trivial), ⟨root, rfl, hOwned⟩, ?_⟩
    intro u y hy _ wy hwy hly b hb c hc
    obtain ⟨hSame, hFresh⟩ := hVars1.regions_after hStepA hy hwy hly fun _ _ => trivial
    rw [hSame] at hc
    exact regionsDisjoint_symm (hFresh c hc b hb)
  -- The index, in local `base + 2`.
  simp only [wpX_constI64_cons]
  have hLow5 : ({ s4 with values := s4.values } : Locals).params.length ≤ base + 2 := by
    show s4.params.length ≤ base + 2; rw [hp4]; omega
  have hHigh5' : base + 2 < s4.positions := by rw [hh4]; omega
  have hHigh5 := Locals.lt_total (s := { s4 with values := s4.values }) hHigh5'
  refine wpX_localSet_local hLow5 hHigh5 ?_
  set s5 := setLocal { s4 with values := s4.values } (base + 2) (.i64 0) with hs5
  have hF5 : Frame base s4 s5 := Frame.setValues hLow5 (by omega) hHigh5'
  have hN5 : s5.get base = some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLow5 (by omega), Locals.get_values]; exact hN4
  have hRoot5 : s5.get (base + 1) = some (.i64 root) := by
    rw [Locals.get_setLocal_ne hLow5 (by omega), Locals.get_values]; exact hRoot4
  have hIdx5 : s5.get (base + 2) = some (.i64 0) := Locals.get_setLocal_same hLow5 hHigh5
  -- The loop.  The invariant holds an array of the count's elements' words whose elements below
  -- the index `i` hold the built ones, and the count less the index decreases.
  refine wpX_block_cons ?_
  refine wpX_loop_cons
    (fun st si => ∃ heapI words, ∃ i : Nat, i ≤ (count.denote funs env).toNat ∧
      words.size = (count.denote funs env).toNat * e.width ∧
      (∀ i', i' < i → ∀ j, j < e.width → words[i' * e.width + j]! =
        (e.toWords (elem.denote funs (.cons (UInt64.ofNat i') env)))[j]!) ∧
      si.get base = some (.i64 (count.denote funs env)) ∧
      si.get (base + 1) = some (.i64 root) ∧ si.get (base + 2) = some (.i64 (UInt64.ofNat i)) ∧
      After env slots (fun i => live i || (Expr.build count elem).uses i)
        (fun i => live i || elem.uses (i + 1)) base heap store s (.array .word) .owned words heapI
        st si [.i64 root] ∧
      (strict = true → heapI.Aligned ∧
        Ty.AlignedVal .owned st (.array .word) [.i64 root] words) ∧
      ((Expr.build count elem).fits funs fits env = true →
        heapI.top.toNat ≤ heap.top.toNat +
          (dyingPot store s env slots paid (fun i => (live i || elem.uses (i + 1)) || count.uses i)
            (fun i => live i || elem.uses (i + 1)) +
          count.allocs funs flags bounds (slots.map Slot.mode) paid (fun i => live i || elem.uses (i + 1))
            env + allocCost (((count.denote funs env).toNat * e.width + 1) * 8) +
          sumBelow
              (fun k => elem.allocs funs flags bounds (.borrowed :: slots.map Slot.mode) (false :: paid)
          (shift 1 (fun i => live i || elem.uses (i + 1))) (.cons (UInt64.ofNat k) env)) i)))
    (fun _ si => match si.get (base + 2) with
      | some (.i64 i) => (count.denote funs env).toNat - i.toNat
      | _ => 0)
    ⟨heap2, words, 0, Nat.zero_le _, hSize, fun _ h => absurd h (Nat.not_lt_zero _), hN5,
      hRoot5, hIdx5, a0.reframe hF5,
      fun hs => ⟨(hAlA hs).2.2, Ty.AlignedVal.ownedArray (hAlA hs).1 (hAlA hs).2.1⟩, fun hd => by
        have := hTopK (hdK hd).1; simp only [sumBelow]; omega⟩ ?_
  rintro st si ⟨heapI, words, i, hi, hSize, hPrefix, hNi, hRooti, hIdxi, aI, hAlI, hInv⟩
  have hi64 : (UInt64.ofNat i).toNat = i :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  simp only [wpX_localGet_cons, Locals.get_values, hIdxi, hNi, wpX_geUI64_cons, wpX_br_if_cons]
  by_cases hDone : count.denote funs env ≤ UInt64.ofNat i
  · -- The array is complete: the release of the outer variables that only the element reads,
    -- and the array's address.
    have hiEq : i = (count.denote funs env).toNat := by
      rw [UInt64.le_iff_toNat_le, hi64] at hDone; omega
    simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte, List.take_zero,
      List.drop_zero, List.nil_append]
    have hWords : words = e.words (LeanExe.build (count.denote funs env)
        fun i => elem.denote funs (.cons i env)) := by
      refine Elem.words_ext e (by rw [hSize]; simp [LeanExe.build]) fun i' hi' j hj => ?_
      have hi'' : i' < (count.denote funs env).toNat := by simpa [LeanExe.build] using hi'
      rw [hPrefix i' (by omega) j hj, getElem!_pos (LeanExe.build (count.denote funs env)
        fun i => elem.denote funs (.cons i env)) i' hi']
      simp [LeanExe.build]
    rw [hWords] at aI
    refine After.releaseX hm hRA (s1 := si) (live := live)
      (sel := fun i => elem.uses (i + 1) && !live i) hVars (After.ofWords aI)
      (fun hs => ⟨HoldsA.after hVars (hAl hs) (After.ofWords aI) (fun i h => by simp only [Expr.uses]; exact live_build _ _ _ h) (hAlI hs).1,
        Ty.AlignedVal.ownedArray (hRootAl hs) (Ty.AlignedVal.arrayCap (hAlI hs).2)⟩)
      (fun i h => by simp only [Expr.uses]; exact live_build _ _ _ h)
      (fun i h => by simp only [Bool.and_eq_true] at h; simp [h.1]) (fun i h => by simp [h])
      fun heap' store' a' hTopR _ hAl' => ?_
    simp only [wpX_localGet_cons, Locals.get_values, hRooti]
    simpa [setLocal, hs2] using hNext heap' store' si [.i64 root] a' hAl' fun hd => top_unpaid rfl (by
      have h1 := hInv hd; have := congrArg UInt64.toNat hTopR
      rw [hiEq] at h1
      rw [hT]; omega)
  -- One more element.
  have hLess : i < (count.denote funs env).toNat := by
    rw [UInt64.le_iff_toNat_le, hi64] at hDone; omega
  simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte]
  -- The element, in the context with the index as variable 0.
  have holdIdx : LocalsHold si (base + 2) Ty.word.types [.i64 (UInt64.ofNat i)] :=
    fun j hj => by
      obtain rfl : j = 0 := by simpa using hj
      simpa [Ty.types, slotIndex] using hIdxi
  have hhi : si.positions = h := aI.frame.positions.trans hh
  have hLE : ∀ j, (shift 1 (fun i => live i || elem.uses (i + 1)) (j + 1) ||
      elem.uses (j + 1)) = true → (live j || elem.uses (j + 1)) = true := fun j h => by
    simp only [shift_add] at h; exact live_dup _ _ h
  have hVarsI : Holds env slots (fun i => live i || elem.uses (i + 1)) (base + 2) heapI st si :=
    aI.holds.mono (by omega)
  have hVarsE := (Holds.push (t := .word) (v := UInt64.ofNat i) (mode := .borrowed)
    (live' := fun j => shift 1 (fun i => live i || elem.uses (i + 1)) j || elem.uses j)
    (hVarsI.live_mono hLE) holdIdx rfl (Holds.Apart.ofScalar rfl)).mono
    (base' := base + 3) (by simp [Ty.width])
  have hSafeI := (hSafe.after hVars aI
    (fun j hj => by simp only [Expr.uses]; exact live_build _ _ _ hj)).1
  have hSafeE : pool.Safe (.cons (t := .word) (UInt64.ofNat i) env)
      (⟨base + 2, .borrowed⟩ :: slots)
      (fun j => shift 1 (fun k => live k || elem.uses (k + 1)) j || elem.uses j) heapI st si :=
    (hSafeI.mono hLE).push holdIdx
      (show Ty.word.Rep .borrowed heapI st [.i64 (UInt64.ofNat i)] (UInt64.ofNat i) from rfl)
      (by simp only [Mode.fresh]; exact fun _ _ _ hMem => nomatch hMem)
  refine elemSpec _ _ (false :: paid) (shift 1 fun i => live i || elem.uses (i + 1)) h (base + 3)
    heapI st si hhi
    (aI.frame.params.trans hpv) hVarsE aI.step.at_
    (fun hs => HoldsA.push ((HoldsA.after hVars (hAl hs) aI (fun i h => by simp only [Expr.uses]; exact live_build _ _ _ h) (hAlI hs).1).live_mono hLE)
      holdIdx rfl (Ty.AlignedVal.scalar rfl)) hSafeE (by rw [aI.step.cap m]; exact hCap)
    (by show si.params.length ≤ base + 3; rw [aI.frame.params]; omega) (by omega)
    hPlace.2 _ _ ((hTrap.part (fun h => by
          cases hw : (Expr.build count elem).fits funs fits env
          · rfl
          · exact absurd ((hdK hw).2 i hLess) (by simpa using h))
        (fun _ => by simp [Expr.aborts]) fun hd hw => hw.of_le (by
          have := hInv (fits_of_not hd)
          have := sumBelow_mono (fun k => elem.allocs funs flags bounds (.borrowed :: slots.map Slot.mode)
              (false :: paid)
            (shift 1 (fun i => live i || elem.uses (i + 1))) (.cons (UInt64.ofNat k) env))
            (show i + 1 ≤ (count.denote funs env).toNat by omega)
          simp only [sumBelow] at this
          rw [hDe]
          simp only [List.map_cons]; rw [hT]; omega) (aI.step.cap m)).imp fun _ h => h)
    fun heapE stE sE wsE aE hAlE hTopE => ?_
  have hRE := Ty.rep_elem.mp aE.rep
  subst hRE
  -- The element's facts for the outer context, after the array's.
  have aE1 := After.bind (base := base + 2) hVarsI
    (After.refl (t := .word) (mode := .borrowed) (v := UInt64.ofNat i)
      (ws := [.i64 (UInt64.ofNat i)]) aI.step.at_ hVarsI (fun _ h => h) rfl rfl
      (Holds.Apart.ofScalar rfl))
    (Frame.refl _ _) holdIdx aE hLE (fun _ h => h) fun _ h => h
  have aE2 := aE1.lower aI.holds (by omega) fun _ h => h
  obtain ⟨hStep, hFrame, hRep1, hApart1, -⟩ := After.seq hVars aI aE2
    (fun i h => by simp only [Expr.uses]; exact live_build _ _ _ h) fun _ h => h
  have aI2 : After env slots (fun i => live i || (Expr.build count elem).uses i)
      (fun i => live i || elem.uses (i + 1)) base heap store s (.array .word) .owned words heapE
      stE sE [.i64 root] :=
    ⟨hStep.mono (fun _ h => h) fun b hb => List.mem_append_left _ hb, hFrame, aE2.holds,
      hRep1, hApart1⟩
  have hpE : sE.params = s.params := aE.frame.params.trans aI.frame.params
  have hhE : sE.positions = h := aE.frame.positions.trans hhi
  have hgetE : ∀ j < base + 3, sE.get j = si.get j := fun j hj => (aE.frame.below j hj).1
  -- The element's words, from local `base + 3` on.
  refine wpX_storeCode (e.values (elem.denote funs (.cons (UInt64.ofNat i) env))) h (base + 3)
    e.types sE si.values (by rw [e.values_length, e.types_length]) hhE
    (by rw [hpE]; omega) (by rw [e.types_length, hhE]; omega)
    fun s6 f6 hold6 _ => ?_
  have hp6 : s6.params = s.params := f6.params.trans hpE
  have hh6 : s6.positions = h := f6.positions.trans hhE
  have hget6 : ∀ j < base + 3, s6.get j = si.get j := fun j hj =>
    (f6.below j hj).1.trans (hgetE j hj)
  -- The position of the element's first word, in local `base + 3 + k`.
  simp only [wpX_localGet_cons, Locals.get_values, hget6 (base + 2) (by omega), hIdxi]
  rw [wpX_scaleCode, words_scale hk
    (lt_of_le_of_lt (Nat.mul_le_mul_right e.width (Nat.le_of_lt hLess)) hck)]
  have hLow7 : ({ s6 with values := si.values } : Locals).params.length ≤ base + 3 + e.width := by
    show s6.params.length ≤ _; rw [hp6]; omega
  have hHigh7' : base + 3 + e.width < s6.positions := by rw [hh6]; omega
  have hHigh7 := Locals.lt_total (s := { s6 with values := si.values }) hHigh7'
  refine wpX_localSet_local hLow7 hHigh7 ?_
  set s7 := setLocal { s6 with values := si.values } (base + 3 + e.width)
    (.i64 (UInt64.ofNat (i * e.width))) with hs7
  have f7 : Frame (base + 3) s6 s7 := Frame.setValues hLow7 (by omega) hHigh7'
  have hW7 : s7.get (base + 3 + e.width) = some (.i64 (UInt64.ofNat (i * e.width))) :=
    Locals.get_setLocal_same hLow7 hHigh7
  have hget7 : ∀ j < base + 3, s7.get j = si.get j := fun j hj =>
    (f7.below j hj).1.trans (hget6 j hj)
  have hh7 : s7.positions = h := f7.positions.trans hh6
  have hold7 : LocalsHold s7 (base + 3) e.types
      (List.zipWith typedValue e.types
        (e.toWords (elem.denote funs (.cons (UInt64.ofNat i) env)))) := by
    rw [e.values_typed]
    intro j hj
    have := hold6 j hj
    rw [e.values_length] at hj
    rw [show s7.positions = s6.positions from f7.positions]
    rw [← this]
    simp only [hs7]
    rw [Locals.get_setLocal_ne hLow7, Locals.get_values]
    cases hty : e.types.getD j .i64 <;> simp only [slotIndex] <;> omega
  -- The writes of the element's words.
  have hik : i * e.width + e.width ≤ words.size := by
    rw [hSize]; have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hLess)
    rw [Nat.succ_mul] at this; exact this
  have hik64 : (UInt64.ofNat (i * e.width)).toNat = i * e.width :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  refine wpX_storeWordsCode hRootAl 0 (base + 3) e.types
    (e.toWords (elem.denote funs (.cons (UInt64.ofNat i) env))) words stE s7
    (aI2.reframe ((f6.mono (by omega)).trans (f7.mono (by omega)))) hh7
    (by rw [hget7 (base + 1) (by omega)]; exact hRooti) hW7 hold7
    (by rw [e.toWords_length, e.types_length]) (e.typed_words _) (by rw [hik64, e.types_length]; omega)
    fun store8 a8 hc8 => ?_
  rw [hik64, Nat.add_zero] at a8
  -- The next index, in local `base + 2`.
  simp only [wpX_localGet_cons, hget7 (base + 2) (by omega), hIdxi, wpX_constI64_cons,
    wpX_addI64_cons]
  have hLow9 : ({ s7 with values := s7.values } : Locals).params.length ≤ base + 2 := by
    show s7.params.length ≤ base + 2; rw [f7.params, hp6]; omega
  have hHigh9' : base + 2 < s7.positions := by rw [hh7]; omega
  have hHigh9 := Locals.lt_total (s := { s7 with values := s7.values }) hHigh9'
  refine wpX_localSet_local (s := s7) (vs := s7.values) hLow9 hHigh9 ?_
  have hSucc : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
    rw [UInt64.ofNat_add]; rfl
  have hSucc64 : (UInt64.ofNat (i + 1)).toNat = i + 1 :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hIdx9 := Locals.get_setLocal_same (v := .i64 (UInt64.ofNat i + 1)) hLow9 hHigh9
  rw [wpX_br_cons]
  dsimp only
  have hfit : i * e.width + (e.toWords (elem.denote funs (.cons (UInt64.ofNat i) env))).length ≤
      words.size := by rw [e.toWords_length]; exact hik
  refine ⟨⟨heapE, _, i + 1, by omega, by rw [writeWords_size, hSize], fun i' hi' j hj => ?_,
    ?_, ?_, by rw [hIdx9, hSucc],
    a8.reframe (Frame.setValues hLow9 (by omega) hHigh9'),
    fun hs => ⟨(hAlE hs).1.1, Ty.AlignedVal.ownedArray (hRootAl hs) (by
      rw [hc8]; exact Ty.AlignedVal.arrayCap (After.alignedSeq' aI aE2 (hAlI hs).2))⟩, ?_⟩, ?_⟩
  · rw [writeWords_getElem! _ _ _ hfit, e.toWords_length]
    by_cases hii : i' = i
    · subst hii
      rw [ite_eq_left (by omega), show i' * e.width + j - i' * e.width = j by omega]
    · have hlt : i' < i := by omega
      have hout : ¬(i * e.width ≤ i' * e.width + j ∧ i' * e.width + j < i * e.width + e.width) := by
        intro ⟨h1, _⟩
        have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hlt)
        rw [Nat.succ_mul] at this; omega
      rw [ite_eq_right hout]
      exact hPrefix i' hlt j hj
  · rw [Locals.get_setLocal_ne hLow9 (by omega), Locals.get_values, hget7 base (by omega)]
    exact hNi
  · rw [Locals.get_setLocal_ne hLow9 (by omega), Locals.get_values, hget7 (base + 1) (by omega)]
    exact hRooti
  · intro hd
    have := hInv hd; have h6 := hTopE ((hdK hd).2 i hLess)
    rw [hDe] at h6
    simp only [List.map_cons] at h6
    simp only [sumBelow]; omega
  · rw [hIdx9]
    simp only [hSucc, hSucc64]
    omega

/-- `LeanExe.build`: the count in local `base`, a trap at `unreachable` when it is `2 ^ 29` or
more, a new owned array at the address in local `base + 1`, and the index in local `base + 2`.
The invariant at the top of the WebAssembly `loop` holds an owned array of the count's length
whose elements below the index are the built ones, with the facts of `After` for the outer
variables live in the loop.  Each iteration runs the element's code in the context with the
index, which keeps every region, and stores the element. -/
theorem spec_build (hm : Runtime m) {Γ' : List Ty} {e : Elem} {count : Expr S Γ' .word}
    {elem : Expr S (.word :: Γ') (.elem e)}
    (countSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv count env
        slots paid live)
    (elemSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv elem env
        slots paid live) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.build count elem) env
        slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_build (strict := false) hm nofun nofun
      (fun env slots paid live => CodeSpecX.false_iff.mpr (countSpec env slots paid live))
      (fun env slots paid live => CodeSpecX.false_iff.mpr (elemSpec env slots paid live)) env slots
      paid live)

/-- `HoldsA.after` for an evolution. -/
theorem HoldsA.evolves {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap' : Heap} {store store' : Store Unit} {s s' : Locals}
    (h0 : Holds env slots L0 base heap store s) (hA : HoldsA env slots L0 heap store s)
    (e : Evolves env slots L0 L base heap store s heap' store' s')
    (hL : ∀ i, L i = true → L0 i = true) (hAl : heap'.Aligned) :
    HoldsA env slots L heap' store' s' := by
  refine ⟨hAl, fun u y hy wy hwy hly => ?_⟩
  have hwy0 := (h0.hold_agree e.frame (hL _ hy) hly).mp hwy
  obtain ⟨_, wy', hold', hRep⟩ := h0.1 u y (hL _ hy)
  obtain rfl := LocalsHold.unique hwy0 hold' (hly.trans hRep.length.symm)
  exact (hA.2 u y (hL _ hy) wy hwy0 hly).step e.step hRep (h0.keepDying hL hy hwy0 hly)

/-- `After.storeWord` under the flag. -/
theorem After.storeWordX {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit} {s s1 : Locals} {mode : Mode}
    {v : UInt64} {vs : List Value} {loc : Nat} {rest : Program} {Q : Assertion Unit}
    (a : After env slots L0 L base heap store s .word mode v heap1 store1 s1 [.i64 v])
    (hLoc : base ≤ loc) (hLow : s.params.length ≤ loc) (hHigh : loc < s.positions)
    (hNext : Evolves env slots L0 L base heap store s heap1 store1
        (setLocal { s1 with values := vs } loc (.i64 v)) →
      (setLocal { s1 with values := vs } loc (.i64 v)).get loc = some (.i64 v) →
      wpX strict m rest Q store1 (setLocal { s1 with values := vs } loc (.i64 v)) host) :
    wpX strict m (.localSet loc :: rest) Q store1 { s1 with values := [.i64 v].reverse ++ vs }
      host := by
  have hLow1 : ({ s1 with values := vs } : Locals).params.length ≤ loc := by
    show s1.params.length ≤ loc; rw [a.frame.params]; exact hLow
  have hHigh1 : loc < ({ s1 with values := vs } : Locals).positions := by
    rw [Locals.positions_values, a.frame.positions]; exact hHigh
  refine wpX_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  have e := a.toEvolves rfl
  have f : Frame base s1 (setLocal { s1 with values := vs } loc (.i64 v)) :=
    Frame.setValues hLow1 hLoc hHigh1
  exact hNext ⟨e.step, e.frame.trans f, e.holds.agree f⟩
    (Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1))

/-- The store of a word value into local `loc`, at or above `base`: the facts of `After` as an
evolution to the locals with the word. -/
theorem After.storeWord {Γ : List Ty} {env : Env Γ} {slots : List Slot} {L0 L : Nat → Bool}
    {base : Nat} {heap heap1 : Heap} {store store1 : Store Unit} {s s1 : Locals} {mode : Mode}
    {v : UInt64} {vs : List Value} {loc : Nat} {rest : Program} {Q : Assertion Unit}
    (a : After env slots L0 L base heap store s .word mode v heap1 store1 s1 [.i64 v])
    (hLoc : base ≤ loc) (hLow : s.params.length ≤ loc) (hHigh : loc < s.positions)
    (hNext : Evolves env slots L0 L base heap store s heap1 store1
        (setLocal { s1 with values := vs } loc (.i64 v)) →
      (setLocal { s1 with values := vs } loc (.i64 v)).get loc = some (.i64 v) →
      wp m rest Q store1 (setLocal { s1 with values := vs } loc (.i64 v)) host) :
    wp m (.localSet loc :: rest) Q store1 { s1 with values := [.i64 v].reverse ++ vs } host :=
  After.storeWordX (strict := false) a hLoc hLow hHigh hNext

/-- `x.set! i.toNat v`: the position in local `base`, the value's words from local `base + 1` on,
the array as owned in local `base + 1 + k`, which is `x`'s own block when `x` is owned and dies,
and, when the position is below the size, the position of the element's first word in local
`base + 2 + k` and the writes of the element's words. -/
theorem specX_set (hCopy : CopyCodeX strict m host) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word} {v : Expr S Γ' (.elem e)}
    (iSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv i env slots paid live)
    (vSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv v env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.set x i v) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi := Nat.le_max_left i.width (max (1 + v.width) (1 + e.width + copyWidth (.array e)))
  have hv := (Nat.le_max_left (1 + v.width) (1 + e.width + copyWidth (.array e))).trans
    (Nat.le_max_right i.width _)
  have hx := (Nat.le_max_right (1 + v.width) (1 + e.width + copyWidth (.array e))).trans
    (Nat.le_max_right i.width _)
  have hcw : copyWidth (Ty.array e) = 4 := rfl
  have hk := e.width_pos
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  have hT : (Expr.set x i v).allocs funs flags bounds (slots.map Slot.mode) paid live env =
      i.allocs funs flags bounds (slots.map Slot.mode) paid
          (fun j => live j || j == x.index || v.uses j) env +
        v.allocs funs flags bounds (slots.map Slot.mode) paid (fun j => live j || j == x.index) env +
        x.ownedCost (slots.map Slot.mode) live (env.get x) := rfl
  have hdS : (Expr.set x i v).fits funs fits env = true →
      i.fits funs fits env = true ∧ v.fits funs fits env = true :=
    fun hd => by simpa [Expr.fits] using hd
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc, List.cons_append, List.nil_append]
  -- The position, in local `base`.
  have hIn : ∀ k, ((live k || k == x.index || v.uses k) || i.uses k) = true →
      (live k || (Expr.set x i v).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact set_live_index _ _ _ _ h
  -- The variables that die in the position and in the value.  The array, when it dies, is
  -- consumed, and its potential is dropped.
  have hDiv : dyingPot store s env slots paid
        (fun k => (live k || k == x.index || v.uses k) || i.uses k)
        (fun k => live k || k == x.index || v.uses k) +
      dyingPot store s env slots paid (fun k => (live k || k == x.index) || v.uses k)
        (fun k => live k || k == x.index) ≤
      dyingPot store s env slots paid (fun k => live k || (Expr.set x i v).uses k) live := by
    rw [dyingPot_split _ (fun k => live k || k == x.index || v.uses k) live
      (fun k h => hIn k (by simp [h])) (fun k h => by simp [h]),
      dyingPot_split (fun k => live k || k == x.index || v.uses k) (fun k => live k || k == x.index)
        live (fun k h => by simp [h]) (fun k h => by simp [h]),
      dyingPot_congr (L0 := fun k => live k || (Expr.set x i v).uses k)
        (L0' := fun k => (live k || k == x.index || v.uses k) || i.uses k)
        (fun k => by simp only [Expr.uses, Bool.or_comm, Bool.or_left_comm])
        fun _ => rfl]
    omega
  refine iSpec env slots paid _ h base heap store s hh hpv
    (hVars.live_mono hIn) hAt (fun hs => (hAl hs).live_mono hIn) (hSafe.mono hIn) hCap hBase (by omega) hPlace.1 _ _
    (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun _ => by simp [Expr.aborts])
      fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hAlI hTopI => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  refine After.storeWordX a1 le_rfl hBase (by rw [hh]; omega) fun e1 hI1 => ?_
  have hp1 := e1.frame.params
  have hh1 := e1.frame.positions.trans hh
  -- The value's words, from local `base + 1` on.
  have hDv : ∀ s1' : Locals, Evolves env slots (fun k => (live k || k == x.index || v.uses k) ||
        i.uses k) (fun k => live k || k == x.index || v.uses k) base heap store s heap1 store1
        s1' →
      dyingPot store1 s1' env slots paid (fun k => (live k || k == x.index) || v.uses k)
        (fun k => live k || k == x.index) =
      dyingPot store s env slots paid (fun k => (live k || k == x.index) || v.uses k)
        (fun k => live k || k == x.index) := fun _ e =>
    dyingPot_evolves (hVars.live_mono hIn) e (fun k h => by simp [h]) _ _ fun _ h => h
  have hAlV0 := fun (hs : strict = true) => HoldsA.evolves (hVars.live_mono hIn)
    ((hAl hs).live_mono hIn) e1 (fun k h => by simp [h]) (hAlI hs).1.1
  refine vSpec env slots paid _ h (base + 1) heap1 store1 _ hh1
    (hp1.trans hpv) (e1.holds.mono (Nat.le_succ base)) e1.step.at_ hAlV0
    ((hSafe.mono hIn).evolves (hVars.live_mono hIn) e1 (fun k hk => by simp [hk])) (by rw [e1.step.cap m]; exact
        hCap)
    (by rw [hp1]; omega) (by omega) hPlace.2 _ _
    (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun _ => by simp [Expr.aborts])
      fun hd hw => by
        have := hTopI (hdS (fits_of_not hd)).1
        rw [hDv _ e1]
        exact hw.shift (c1 := dyingPot store s env slots paid
            (fun k => (live k || k == x.index || v.uses k) || i.uses k)
            (fun k => live k || k == x.index || v.uses k) +
            i.allocs funs flags bounds (slots.map Slot.mode) paid
              (fun j => live j || j == x.index || v.uses j) env)
          (by omega) (by rw [hT]; omega) (e1.step.cap m))
    fun heap2 store2 s2 ws2 a2 hAlV hTopV => ?_
  have hR2 := Ty.rep_elem.mp a2.rep
  subst hR2
  have e2a := a2.toEvolves rfl
  have hp2a : s2.params = s.params := e2a.frame.params.trans hp1
  have hh2a : s2.positions = h := e2a.frame.positions.trans hh1
  refine wpX_storeCode (e.values (v.denote funs env)) h (base + 1) e.types s2 s.values
    (by rw [e.values_length, e.types_length]) hh2a (by rw [hp2a]; omega)
    (by rw [e.types_length, hh2a]; omega) fun s2' f2 hold2 _ => ?_
  have f2' : Frame (base + 1) s2 { s2' with values := s.values } := f2.trans Frame.ofValues
  have e2 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) (base + 1) heap1 store1 _ heap2 store2
      { s2' with values := s.values } :=
    ⟨e2a.step, e2a.frame.trans f2', e2a.holds.agree f2'⟩
  have hp2 : s2'.params = s.params := f2.params.trans hp2a
  have hh2 : s2'.positions = h := f2.positions.trans hh2a
  have hI2 : s2'.get base = some (.i64 (i.denote funs env)) :=
    (e2.frame.below base (by omega)).1.trans hI1
  -- The array as owned, in local `base + 1 + k`.
  refine specX_ownedVar hCopy x (s := { s2' with values := s.values }) hh2 (hp2.trans hpv)
    ((e2.holds.mono (by omega)) : Holds env slots
      (fun k => live k || k == x.index) (base + 1 + e.width) heap2 store2 _) e2.step.at_
    (fun hs => HoldsA.evolves (e1.holds.mono (Nat.le_succ base)) (hAlV0 hs) e2
      (fun k h => by simp [h]) (hAlV hs).1.1)
    (((hSafe.mono hIn).evolves (hVars.live_mono hIn) e1 (fun k hk => by simp [hk])).evolves
      (e1.holds.mono (Nat.le_succ base)) e2 (fun k hk => by simp [hk]))
    (by rw [e2.step.cap m, e1.step.cap m]; exact hCap)
    (by show s2'.params.length ≤ _; rw [hp2]; omega)
    (by omega) (hTrap.alloc (by simp [Expr.aborts]) fun hd hw => hw.of_le (by
      have := hTopI (hdS (fits_of_not hd)).1; have h2 := hTopV (hdS (fits_of_not hd)).2
      rw [hDv _ e1] at h2
      rw [hT]; omega)
      (by rw [e2.step.cap m, e1.step.cap m]))
    fun heap3 store3 s3 ws3 a3 hAlO hTopO => ?_
  obtain ⟨p, hws, hOwned⟩ := a3.rep
  subst hws
  have hPAl : strict = true → p.toNat % 8 = 0 := fun hs => Ty.AlignedVal.array hOwned (hAlO hs).2
  have hp3 : s3.params = s.params := a3.frame.params.trans hp2
  have hh3 : s3.positions = h := a3.frame.positions.trans hh2
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow3 : ({ s3 with values := s.values } : Locals).params.length ≤ base + 1 + e.width := by
    show s3.params.length ≤ _; rw [hp3]; omega
  have hHigh3' : base + 1 + e.width < s3.positions := by rw [hh3]; omega
  have hHigh3 := Locals.lt_total (s := { s3 with values := s.values }) hHigh3'
  refine wpX_localSet_local hLow3 hHigh3 ?_
  set s4 : Locals := setLocal { s3 with values := s.values } (base + 1 + e.width) (.i64 p)
    with hs4
  have hP4 : s4.get (base + 1 + e.width) = some (.i64 p) := Locals.get_setLocal_same hLow3 hHigh3
  have hF4 : Frame (base + 1 + e.width) s3 s4 := Frame.setValues hLow3 le_rfl hHigh3'
  have hI4 : s4.get base = some (.i64 (i.denote funs env)) :=
    (hF4.below base (by omega)).1.trans ((a3.frame.below base (by omega)).1.trans hI2)
  have hold4 : LocalsHold s4 (base + 1) e.types (e.values (v.denote funs env)) :=
    (LocalsHold.frame (Frame.ofValues.trans (a3.frame.trans hF4))
      (by rw [e.values_length, e.types_length]) (by rw [e.types_length])).mpr hold2
  have hh4 : s4.positions = h := hF4.positions.trans hh3
  have hp4 : s4.params = s.params := hF4.params.trans hp3
  have hValues4 : s4.values = s.values := rfl
  have a4 := a3.reframe hF4
  -- The rest of the code, from the array after the writes or without them.
  have hFinish : ∀ (store4 : Store Unit) (s' : Locals) (ws : Array UInt64),
      Frame (base + 1 + e.width) s4 s' → s'.values = s.values →
      ws = e.words ((env.get x).set! (i.denote funs env).toNat (v.denote funs env)) →
      After env slots (fun k => live k || k == x.index) live (base + 1 + e.width) heap2 store2
        { s2' with values := s.values } (.array .word) .owned ws heap3 store4 s' [.i64 p] →
      (strict = true → heap3.Aligned ∧ Ty.AlignedVal .owned store4 (.array .word) [.i64 p] ws) →
      wpX strict m rest Q store4 { s' with values := .i64 p :: s'.values } host := by
    rintro store4 s' ws _ hv' rfl aX hAlX
    have aX1 := (After.ofWords aX).lower e2.holds (by omega) fun k h => by simp [h]
    have aX2 := After.prepend (e1.holds.mono (Nat.le_succ base)) e2 aX1
      (fun k h => by simp [h]) fun k h => by simp [h]
    have aX3 := After.prepend (hVars.live_mono hIn) e1 (aX2.lower e1.holds (Nat.le_succ base)
      fun k h => by simp [h]) (fun k h => by simp [h]) fun k h => by simp [h]
    simpa [hv'] using hNext heap3 store4 _ [.i64 p] (aX3.liveIn hIn)
      (fun hs => ⟨HoldsA.after hVars (hAl hs) (aX3.liveIn hIn) (fun k h => by simp [h]) (hAlX hs).1,
        Ty.AlignedVal.ownedArray (hPAl hs) (Ty.AlignedVal.arrayCap (hAlX hs).2)⟩) fun hd => top_unpaid rfl (by
      have := hTopI (hdS hd).1; have h2 := hTopV (hdS hd).2
      rw [hDv _ e1] at h2
      rw [hT]; omega)
  have hA := hOwned.values
  have hLength := hA.lengthBound
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  have hn64 : (env.get x).size < UInt64.size := by
    have := Nat.le_mul_of_pos_right (env.get x).size hk
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega
  show wpX strict m _ Q store3 s4 host
  simp only [wpX_localGet_cons, Locals.get_values, hI4, hP4, wpX_wrapI64_cons, wpX_load64_cons,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size, wpX_divCode hk, words_div hk hnk]
  refine ⟨fun hs => UInt64.toUInt32_mod8 (hPAl hs), ?_⟩
  simp only [wpX_ltUI64_cons]
  refine wpX_iff_cons rfl ?_
  have hLess : i.denote funs env < UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat < (env.get x).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hn64]
  by_cases hc : (i.denote funs env).toNat < (env.get x).size
  · -- The writes of the element's words.
    rw [ite_eq_left (by simp [hLess.mpr hc])]
    have hik : (i.denote funs env).toNat * e.width < 536870912 :=
      lt_of_le_of_lt (Nat.mul_le_mul_right e.width (Nat.le_of_lt hc)) hnk
    simp only [wpX_localGet_cons, Locals.get_values, hI4]
    have hs := words_scale hk hik
    rw [UInt64.ofNat_toNat] at hs
    rw [wpX_scaleCode, hs]
    have hLow5 : ({ s4 with values := s4.values } : Locals).params.length ≤
        base + 2 + e.width := by
      show s4.params.length ≤ _; rw [hp4]; omega
    have hHigh5' : base + 2 + e.width < s4.positions := by rw [hh4]; omega
    have hHigh5 := Locals.lt_total (s := { s4 with values := s4.values }) hHigh5'
    refine wpX_localSet_local hLow5 hHigh5 ?_
    set s5 : Locals := setLocal { s4 with values := s4.values } (base + 2 + e.width)
      (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) with hs5
    have hF5 : Frame (base + 2 + e.width) s4 s5 := Frame.setValues hLow5 le_rfl hHigh5'
    have hW5 : s5.get (base + 2 + e.width) =
        some (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) :=
      Locals.get_setLocal_same hLow5 hHigh5
    have hP5 : s5.get (base + 1 + e.width) = some (.i64 p) :=
      (hF5.below _ (by omega)).1.trans hP4
    have hold5 : LocalsHold s5 (base + 1) e.types
        (List.zipWith typedValue e.types (e.toWords (v.denote funs env))) := by
      rw [e.values_typed]
      exact (LocalsHold.frame hF5 (by rw [e.values_length, e.types_length])
        (by rw [e.types_length]; omega)).mpr hold4
    have hik64 : (UInt64.ofNat ((i.denote funs env).toNat * e.width)).toNat =
        (i.denote funs env).toNat * e.width :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    rw [← List.append_nil (storeWordsCode h (base + 1 + e.width) (base + 2 + e.width) 0 (base + 1)
      e.types)]
    refine wpX_storeWordsCode hPAl 0 (base + 1) e.types (e.toWords (v.denote funs env))
      (e.words (env.get x)) store3 s5 (a4.toWords.reframe (hF5.mono (by omega)))
      (hF5.positions.trans hh4) hP5 hW5 hold5 (by rw [e.toWords_length, e.types_length]) (e.typed_words _)
      (by rw [hik64, e.types_length, Elem.words_size]
          have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hc)
          rw [Nat.succ_mul] at this; omega)
      fun store6 a6 hc6 => ?_
    rw [hik64] at a6
    simp only [Nat.add_zero] at a6
    rw [Elem.words_set e hc] at a6
    rw [wpX_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, hP5]
    exact hFinish store6 s5 _ (hF5.mono (by omega)) rfl rfl a6
      (fun hs => ⟨(hAlO hs).1.1, Ty.AlignedVal.ownedArray (hPAl hs) (by rw [hc6]; exact Ty.AlignedVal.arrayCap (hAlO hs).2)⟩)
  · rw [ite_eq_right (by simp [hLess, hc])]
    rw [wpX_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, wpX_localGet_cons, hP4]
    exact hFinish _ s4 (e.words (env.get x)) (Frame.refl _ _) rfl
      (by simp [Array.set!, Array.setIfInBounds, hc]) a4.toWords
      (fun hs => ⟨(hAlO hs).1.1, Ty.AlignedVal.ownedArray (hPAl hs) (Ty.AlignedVal.arrayCap (hAlO hs).2)⟩)

/-- `Var.roomCode`: an owned array, at the address in local `b + 4`, whose first elements are
those of `x`, whose length is `x`'s length plus the word `e` in local `ext`, and whose block has
room for that length.  An owned `x` that dies is consumed, and any other `x` is read.  The code
traps only when `top` cannot rise by the potential of the paid owned variables that die plus
`Var.roomCost` within the cap.  `top` after the code, plus the potential of the array when `x` is
owned and dies, is at most `top` before it plus that sum. -/
theorem specX_room (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (hRt : strict = true → AllocAligned m) {Γ' : List Ty} {el : Elem} (x : Var Γ' (.array el))
    {env : Env Γ'}
    {slots : List Slot} {paid : List Bool} {live : Nat → Bool} {b ext : Nat} {e : UInt64}
    {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit}
    (hVars : Holds env slots (fun i => live i || i == x.index) b heap store s)
    (hAt : heap.At store)
    (hAl : strict = true → HoldsA env slots (fun i => live i || i == x.index) heap store s)
    (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ b)
    (hRoom : b + 6 ≤ s.positions) (hExt : s.get ext = some (.i64 e))
    (hExtB : ext < b) (he : e.toNat ≤ 536870912)
    (hTrap : TrapOK (!decide (heap.Within store m
      (dyingPot store s env slots paid (fun i => live i || i == x.index) live +
        x.roomCost (slots.map Slot.mode) paid live (env.get x) e.toNat))) Q)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (q : UInt64)
      (words : Array UInt64), words.size = (el.words (env.get x)).size + e.toNat →
      (∀ j (hj : j < (el.words (env.get x)).size), words[j]! = (el.words (env.get x))[j]) →
      After env slots (fun i => live i || i == x.index) live b heap store s (.array .word) .owned
        words heap' store' s' [.i64 q] →
      s'.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) →
      s'.get (b + 4) = some (.i64 q) → s'.values = s.values →
      (strict = true → heap'.Aligned ∧ Ty.AlignedVal .owned store' (.array .word) [.i64 q] words) →
      heap'.top.toNat +
          (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
            arrayPot store' q words.size else 0) ≤
        heap.top.toNat + dyingPot store s env slots paid (fun i => live i || i == x.index) live +
          x.roomCost (slots.map Slot.mode) paid live (env.get x) e.toNat →
      wpX strict m rest Q store' s' host) :
    wpX strict m (x.roomCode slots b live ext ++ rest) Q store s host := by
  have hTot : 2 * s.positions ≤ s.params.length + s.locals.length := by
    simp only [Locals.positions]; omega
  obtain ⟨hBelowX, ws, hold, hRep⟩ := hVars.get x (by simp)
  obtain ⟨p, rfl, hArr⟩ := hRep
  have hPAl : strict = true → p.toNat % 8 = 0 := fun hs =>
    Ty.AlignedVal.array hArr ((hAl hs).2 _ x (by simp) [.i64 p] hold rfl)
  -- The potential of `x` when it is paid and dies, which `dyingPot` counts.
  have hPotX : (slots.getD x.index default).mode = .owned → live x.index = false →
      paidAt paid x.index = true →
      arrayPot store p (el.words (env.get x)).size ≤
        dyingPot store s env slots paid (fun i => live i || i == x.index) live :=
    fun hOw hDd hp => by
      have := dyingPot_var (store := store) (s := s) (env := env) (paid := paid)
        (liveIn := fun i => live i || i == x.index) x (by simp) hDd hp hOw
      rw [Env.potOf, hold.read_eq rfl] at this
      exact this
  have hModes : ∀ P : Prop,
      ((slots.getD x.index default).mode = .owned ∧ live x.index = false ↔ P) →
      (modeAt (slots.map Slot.mode) x.index = .owned ∧ live x.index = false ↔ P) := fun P h => by
    rw [modeAt, Slot.modes_getD]; exact h
  have hB := hArr.borrow
  have hA := hB.values
  have hLenB := hA.lengthBound
  have hFitA := hA.1
  have hn : (el.words (env.get x)).size < 536870912 := by omega
  have hN : (UInt64.ofNat (el.words (env.get x)).size).toNat = (el.words (env.get x)).size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hP : s.get (slots.getD x.index default).loc = some (.i64 p) := by
    exact LocalsHold.word hold
  simp only [Var.roomCode, List.append_assoc, List.cons_append, List.nil_append]
  -- The address, in local `b`.
  simp only [wpX_localGet_cons, hP]
  refine wpX_localSet_local hBase (by omega) ?_
  have hLow0 : ({ s with values := s.values } : Locals).params.length ≤ b := hBase
  let s1 := setLocal { s with values := s.values } b (.i64 p)
  have hP1 : s1.get b = some (.i64 p) := Locals.get_setLocal_same hLow0 (by omega)
  have hExt1 : s1.get ext = some (.i64 e) := by
    rw [Locals.get_setLocal_ne hLow0 (by omega)]; exact hExt
  -- The length, in local `b + 1`.
  show wpX strict m _ Q store s1 host
  simp only [wpX_localGet_cons, hP1, wpX_wrapI64_cons, wpX_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead]
  refine ⟨fun hs => UInt64.toUInt32_mod8 (hPAl hs), ?_⟩
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ b + 1 := by
    show s.params.length ≤ b + 1; omega
  have hHigh1 : b + 1 < ({ s1 with values := s.values } : Locals).params.length +
      ({ s1 with values := s.values } : Locals).locals.length := by
    show b + 1 < s.params.length + (setLocal _ _ _).locals.length; simp [setLocal]; omega
  refine wpX_localSet_local hLow1 hHigh1 ?_
  let s2 := setLocal { s1 with values := s.values } (b + 1)
    (.i64 (UInt64.ofNat (el.words (env.get x)).size))
  have hN2 : s2.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) :=
    Locals.get_setLocal_same hLow1 hHigh1
  have hP2 : s2.get b = some (.i64 p) := by
    rw [Locals.get_setLocal_ne hLow1 (by omega)]; exact hP1
  have hExt2 : s2.get ext = some (.i64 e) := by
    rw [Locals.get_setLocal_ne hLow1 (by omega)]; exact hExt1
  -- The new length, in local `b + 2`.
  show wpX strict m _ Q store s2 host
  simp only [wpX_localGet_cons, Locals.get_values, hN2, hExt2, wpX_addI64_cons]
  have hLow2 : ({ s2 with values := s.values } : Locals).params.length ≤ b + 2 := by
    show s.params.length ≤ b + 2; omega
  have hHigh2 : b + 2 < ({ s2 with values := s.values } : Locals).params.length +
      ({ s2 with values := s.values } : Locals).locals.length := by
    show b + 2 < s.params.length + (setLocal _ _ _).locals.length; simp [s1, setLocal]; omega
  refine wpX_localSet_local hLow2 hHigh2 ?_
  let s3 := setLocal { s2 with values := s.values } (b + 2)
    (.i64 (UInt64.ofNat (el.words (env.get x)).size + e))
  have hT3 : s3.get (b + 2) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) :=
    Locals.get_setLocal_same hLow2 hHigh2
  have hN3 : s3.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) := by
    rw [Locals.get_setLocal_ne hLow2 (by omega)]; exact hN2
  have hP3 : s3.get b = some (.i64 p) := by
    rw [Locals.get_setLocal_ne hLow2 (by omega)]; exact hP2
  have hTotal : (UInt64.ofNat (el.words (env.get x)).size + e).toNat =
      (el.words (env.get x)).size + e.toNat := by
    rw [UInt64.toNat_add, hN]; omega
  -- The trap when the new length is `2 ^ 29` or more.
  show wpX strict m _ Q store s3 host
  simp only [wpX_localGet_cons, hT3, wpX_constI64_cons, wpX_geUI64_cons]
  refine wpX_iff_cons rfl ?_
  by_cases hBig : (536870912 : UInt64) ≤ UInt64.ofNat (el.words (env.get x)).size + e
  · simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
    rw [wpX_unreachable_cons]
    have hW : ¬heap.Within store m
        (dyingPot store s env slots paid (fun i => live i || i == x.index) live +
          x.roomCost (slots.map Slot.mode) paid live (env.get x) e.toNat) := by
      rw [UInt64.le_iff_toNat_le, hTotal] at hBig
      simp only [UInt64.reduceToNat] at hBig
      intro hw
      unfold Heap.Within at hw
      have hws := Elem.words_size el (env.get x)
      by_cases hMv : (slots.getD x.index default).mode = .owned ∧ live x.index = false
      · have hO : heap.Owned store p (el.words (env.get x)) := by rw [hMv.1] at hArr; exact hArr
        have hAddr := hO.address
        have hL := room_long (n := (el.words (env.get x)).size)
          (t := (el.words (env.get x)).size + e.toNat) (c := capacityAt store p) hBig (by omega)
          (by omega)
        rw [Var.roomCost_move x paid (env.get x) e.toNat ((hModes _ Iff.rfl).mpr hMv)] at hw
        cases hp : paidAt paid x.index
        · simp only [hp, Bool.false_eq_true, ↓reduceIte, allocCost] at hw; omega
        · have := hPotX hMv.1 hMv.2 hp
          simp only [hp, ↓reduceIte, allocCost] at hw
          simp only [arrayPot] at this
          omega
      · rw [Var.roomCost_copy x paid (env.get x) e.toNat
          (fun h => hMv ((hModes _ Iff.rfl).mp h))] at hw
        have hL := room_long (n := 0) (t := (el.words (env.get x)).size + e.toNat) (c := 0) hBig
          (by omega) (by omega)
        simp only [allocCost] at hw; omega
    exact (hTrap.of_imp (a := true) fun _ => by simpa using hW) _
  simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte]
  rw [wpX_nil]
  dsimp only
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  have hTotalLt : (el.words (env.get x)).size + e.toNat < 536870912 := by
    have := UInt64.not_le.mp hBig
    rw [UInt64.lt_iff_toNat_lt, hTotal] at this
    exact this
  have hT3' : ({ s3 with values := s3.values } : Locals).get (b + 2) =
      some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) := hT3
  have frame3 : Frame b s s3 := by
    have f1 : Frame b s s1 := Frame.setValues hLow0 le_rfl (by omega)
    have f2 : Frame b s1 s2 := Frame.setValues hLow1 (by omega) (by
      simp only [s1, Locals.positions_setLocal]
      omega)
    have f3 : Frame b s2 s3 := Frame.setValues hLow2 (by omega) (by
      simp only [s2, s1, Locals.positions_setLocal, Locals.positions_values]
      omega)
    exact f1.trans (f2.trans f3)
  have hFrame3 := frame3.below
  have hh3 : s3.positions = s.positions := by simp [s3, s2, s1]
  have hp3 : s3.params = s.params := rfl
  have hl3 : s3.locals.length = s.locals.length := by simp [s3, s2, s1, setLocal]
  have hv3 : s3.values = s.values := rfl
  by_cases hMove : (slots.getD x.index default).mode = .owned ∧ live x.index = false
  swap
  · -- A copy into a block with room.
    rw [ite_eq_right hMove]
    simp only [List.cons_append, List.append_assoc, wpX_localGet_cons, hT3', wpX_constI64_cons,
      wpX_addI64_cons, wpX_mulI64_cons]
    have hBytes : ((UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8).toNat =
        8 * ((UInt64.ofNat (el.words (env.get x)).size + e).toNat + 1) := by
      simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.reduceToNat] at hTotal ⊢
      omega
    have hc : allocCost (allocSize ((UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8)).toNat ≤
        x.roomCost (slots.map Slot.mode) paid live (env.get x) e.toNat := by
      have h1 := allocSize_le_mul (k := (el.words (env.get x)).size + e.toNat + 1)
        (bytes := (UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8)
        (by rw [hBytes]; omega) (by rw [hBytes, hTotal]; omega) (by rw [hBytes, hTotal])
      rw [Var.roomCost_copy x paid (env.get x) e.toNat (fun h => hMove ((hModes _ Iff.rfl).mp h)),
        ← Elem.words_size el (env.get x)]
      simp only [allocCost] at h1 ⊢
      omega
    refine wpX_allocCopy hm hRt hAt (fun hs => (hAl hs).1) hPAl hCap (le_trans hc (Nat.le_add_left _ _)) hTrap hB
      (by rw [hTotal]; exact hTotalLt)
      (by omega)
      (by rw [hBytes]) (by rw [hBytes, hTotal]; omega) hP3 hT3 hN3
      (by show s.params.length ≤ b + 4; omega) (by rw [hp3, hl3]; omega)
      (by show s.params.length ≤ b + 5; omega) (by rw [hp3, hl3]; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      fun heap1 store1 s4 q words hSize hPrefix hStep hOwnedQ _ hp4 hl4 hOther4 hQ4 hv4 hTop4 hAlq => ?_
    have hF4 : Frame b s s4 := ⟨hp4.trans hp3, hl4.trans hl3, fun j hj =>
      ⟨by rw [hOther4 j (by omega) (by omega), (hFrame3 j hj).1],
        by rw [hOther4 _ (by omega) (by omega), (hFrame3 j hj).2]⟩,
      fun j hj => by rw [hOther4 _ (by omega) (by omega), frame3.below32 j hj]⟩
    have hVarsL := hVars.live_mono (live' := live) fun i h => by simp [h]
    refine hNext heap1 store1 s4 q words (by rw [hSize, hTotal]) hPrefix ⟨?_, hF4, ?_,
      ⟨q, rfl, hOwnedQ⟩, ?_⟩ (by rw [hOther4 _ (by omega) (by omega)]; exact hN3) hQ4
      (by rw [hv4, hv3])
      (fun hs => ⟨(hAlq hs).2.2, Ty.AlignedVal.ownedArray (hAlq hs).1 (hAlq hs).2.1⟩)
      (by rw [ite_eq_right hMove]; omega)
    · exact hStep.mono (fun _ _ => trivial) fun _ h => h
    · exact (hVarsL.step hStep fun _ _ _ _ _ _ _ _ => trivial).frame hF4 le_rfl
    · intro u y hy _ wy hwy hly c hc d hd
      have hwy' := (hVarsL.hold_agree hF4 hy hly).mp hwy
      obtain ⟨hSame, hFresh⟩ := hVarsL.regions_after hStep hy hwy' hly fun _ _ => trivial
      rw [hSame] at hd
      exact regionsDisjoint_symm (hFresh d hd c hc)
  -- An owned `x` that dies: its block, extended in place or replaced by a larger one.
  obtain ⟨hOwnedX, hDead⟩ := hMove
  rw [ite_eq_left (show (slots.getD x.index default).mode = .owned ∧ live x.index = false from
    ⟨hOwnedX, hDead⟩)]
  have hOwned : heap.Owned store p (el.words (env.get x)) := by rw [hOwnedX] at hArr; exact hArr
  have hCapXAl : strict = true → capacityAt store p % 8 = 0 := fun hs => by
    have h := (hAl hs).2 _ x (by simp) [.i64 p] hold rfl
    rw [hOwnedX] at h
    exact Ty.AlignedVal.arrayCap h
  have hCost := Var.roomCost_move x paid (env.get x) e.toNat
    ((hModes _ Iff.rfl).mpr ⟨hOwnedX, hDead⟩)
  have hws := Elem.words_size el (env.get x)
  have hBaseP := hOwned.base
  have hAddrP := hOwned.address
  have hBelowP := hOwned.below
  have hTop := hAt.top
  have hCapacityP := hOwned.capacity
  have a0 := (After.move x hVars hAt hOwnedX hDead hold rfl).reframe frame3
  have hP3' : ({ s3 with values := s3.values } : Locals).get b = some (.i64 p) := hP3
  have hCapAddr : (p - 32).toUInt32.toNat = p.toNat - 32 :=
    headerAddress_toNat (by simp only [UInt64.reduceToNat]; omega) (by omega)
  -- The capacity, in local `b + 3`.
  simp only [List.cons_append, List.nil_append, wpX_localGet_cons, hP3', wpX_constI64_cons,
    wpX_subI64_cons, wpX_wrapI64_cons, wpX_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by rw [hCapAddr]; omega)]
  refine ⟨fun hs => UInt64.toUInt32_mod8 (UInt64.sub_mod8 (hPAl hs) rfl), ?_⟩
  have hLow3 : ({ s3 with values := s3.values } : Locals).params.length ≤ b + 3 := by
    show s.params.length ≤ b + 3; omega
  have hHigh3 : b + 3 < ({ s3 with values := s3.values } : Locals).params.length +
      ({ s3 with values := s3.values } : Locals).locals.length := by
    show b + 3 < s3.params.length + s3.locals.length; rw [hp3, hl3]; omega
  refine wpX_localSet_local hLow3 hHigh3 ?_
  let s4 := setLocal { s3 with values := s3.values } (b + 3)
    (.i64 (store.mem.read64 (p - 32).toUInt32))
  have hC4 : s4.get (b + 3) = some (.i64 (store.mem.read64 (p - 32).toUInt32)) :=
    Locals.get_setLocal_same hLow3 hHigh3
  have hT4 : s4.get (b + 2) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]; exact hT3
  have hN4 : s4.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]; exact hN3
  have hP4 : s4.get b = some (.i64 p) := by
    rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]; exact hP3
  have hp4 : s4.params = s.params := rfl
  have hl4 : s4.locals.length = s.locals.length := by simp [s4, setLocal, hl3]
  have hF4 : Frame b s3 s4 := ⟨rfl, by simp [s4, setLocal], fun j hj =>
    ⟨by rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values],
      by rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]⟩,
    fun j hj => by rw [Locals.get_setLocal_ne hLow3 (by omega), Locals.get_values]⟩
  have hh4 : s4.positions = s.positions := by simp [s4, hh3]
  have hcN : (store.mem.read64 (p - 32).toUInt32).toNat = capacityAt store p := rfl
  -- The room test.
  show wpX strict m _ Q store s4 host
  simp only [wpX_localGet_cons, Locals.get_values, hT4, hC4, wpX_constI64_cons, wpX_addI64_cons,
    wpX_mulI64_cons, wpX_leUI64_cons]
  refine wpX_iff_cons rfl ?_
  have hNeed : ((UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8).toNat =
      8 * ((el.words (env.get x)).size + e.toNat + 1) := by
    simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.reduceToNat] at hTotal ⊢
    omega
  by_cases hFits : (UInt64.ofNat (el.words (env.get x)).size + e + 1) * 8 ≤
    store.mem.read64 (p - 32).toUInt32
  · -- Room in the block: the new length, in place.
    simp (config := { decide := true }) only [hFits, ↓reduceIte]
    rw [UInt64.le_iff_toNat_le, hNeed, hcN] at hFits
    have hP4' : ({ s4 with values := s4.values } : Locals).get b = some (.i64 p) := hP4
    simp only [wpX_localGet_cons, hP4']
    have hLow4 : ({ s4 with values := s4.values } : Locals).params.length ≤ b + 4 := by
      show s.params.length ≤ b + 4; omega
    have hHigh4 : b + 4 < ({ s4 with values := s4.values } : Locals).params.length +
        ({ s4 with values := s4.values } : Locals).locals.length := by
      show b + 4 < s4.params.length + s4.locals.length; rw [hp4, hl4]; omega
    refine wpX_localSet_local hLow4 hHigh4 ?_
    let s5 := setLocal { s4 with values := s4.values } (b + 4) (.i64 p)
    have hQ5 : s5.get (b + 4) = some (.i64 p) := Locals.get_setLocal_same hLow4 hHigh4
    have hT5 : s5.get (b + 2) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) := by
      rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]; exact hT4
    have hN5 : s5.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) := by
      rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]; exact hN4
    have hF5 : Frame b s4 s5 := ⟨rfl, by simp [s5, setLocal], fun j hj =>
      ⟨by rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values],
        by rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]⟩,
      fun j hj => by rw [Locals.get_setLocal_ne hLow4 (by omega), Locals.get_values]⟩
    show wpX strict m _ _ store s5 host
    have hP32 : p.toUInt32.toNat = p.toNat := by rw [Memory.toUInt32_toNat]; omega
    simp only [wpX_localGet_cons, Locals.get_values, hQ5, hT5, wpX_wrapI64_cons, wrap_toUInt32,
      wpX_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by rw [hP32]; omega), wpX_nil]
    refine ⟨fun hs => UInt64.toUInt32_mod8 (hPAl hs), ?_⟩
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    -- The block holds the new length, the elements of `x`, and what memory held after them.
    let store' : Store Unit :=
      { store with
        mem := store.mem.write64 p.toUInt32 (UInt64.ofNat (el.words (env.get x)).size + e) }
    let words : Array UInt64 :=
      Array.ofFn (n := (UInt64.ofNat (el.words (env.get x)).size + e).toNat) fun j =>
        if j.val < (el.words (env.get x)).size then (el.words (env.get x))[j.val]!
        else store'.mem.read64 (UInt64Array.wordAddress p (j.val + 1))
    have hSize : words.size = (UInt64.ofNat (el.words (env.get x)).size + e).toNat :=
      Array.size_ofFn
    have hValues : UInt64Array.At store' p words := by
      refine ⟨by rw [hSize, hTotal]; omega, ?_, ?_, fun j hj => ?_⟩
      · rw [hSize, hTotal]; simp only [store', Wasm.Mem.write64_pages]; omega
      · rw [hSize, UInt64.ofNat_toNat]; exact Memory.read64_write64 ..
      · simp only [words, Array.getElem_ofFn]
        rw [hSize, hTotal] at hj
        split
        · next hjn =>
          rw [getElem!_pos _ j hjn, ← hA.elementRead j hjn]
          refine Memory.read64_write64_disjoint _ _ _ _ (Or.inr ?_)
          rw [hP32, ← UInt64Array.wordAddress, UInt64Array.wordAddress_toNat hFitA (by omega)]
          omega
        · rfl
    have hWrites : Memory.WritesRange store store' p.toNat (p.toNat + 8) :=
      Memory.WritesRange.write64 _ p.toUInt32 _ _ _ (by omega) (by omega)
    have hWithin : WritesWithin store store' p.toNat (capacityAt store p) :=
      ⟨by rw [hWrites.1], hWrites.2.1, fun a ha => hWrites.2.2 a (by omega)⟩
    have aW := ((a0.toWords.reframe hF4).reframe hF5).rewrite hWithin (by rw [hWrites.1]) hValues
      (by rw [hSize, hTotal]; omega)
    have hCapSame : capacityAt store' p = capacityAt store p := by
      unfold capacityAt
      dsimp only [store']
      rw [Memory.read64_write64_disjoint _ _ _ _ (Or.inl (by rw [hCapAddr, hP32]; omega))]
    refine hNext heap store' _ p words (by rw [hSize, hTotal]) (fun j hj => ?_) aW hN5 hQ5 rfl
      (fun hs => ⟨(hAl hs).1, Ty.AlignedVal.ownedArray (hPAl hs) (by rw [hCapSame]; exact hCapXAl hs)⟩)
      (by
        rw [ite_eq_left ⟨hOwnedX, hDead⟩, hCost]
        simp only [arrayPot, hCapSame, hSize, hTotal]
        cases hp : paidAt paid x.index
        · have := room_inplace_unpaid (n := (el.words (env.get x)).size)
            (t := (el.words (env.get x)).size + e.toNat) hCapacityP (by omega)
          simp only [Bool.false_eq_true, ↓reduceIte, allocCost]; omega
        · have h1 := hPotX hOwnedX hDead hp
          have := room_inplace_paid (n := (el.words (env.get x)).size)
            (t := (el.words (env.get x)).size + e.toNat) (c := capacityAt store p) (by omega)
          simp only [↓reduceIte, allocCost]; simp only [arrayPot] at h1; omega)
    rw [getElem!_pos words j (by rw [hSize, hTotal]; omega)]
    simp only [words, Array.getElem_ofFn]
    rw [ite_eq_left hj, getElem!_pos _ j hj]
  · -- No room: a block of at least twice the capacity, then the release of the old one.
    simp (config := { decide := true }) only [hFits, ↓reduceIte]
    have hT4' : ({ s4 with values := s4.values } : Locals).get (b + 2) =
        some (.i64 (UInt64.ofNat (el.words (env.get x)).size + e)) := hT4
    have hC4' : ({ s4 with values := s4.values } : Locals).get (b + 3) =
        some (.i64 (store.mem.read64 (p - 32).toUInt32)) := hC4
    refine wpX_requestCode hT4' hC4' (by rw [hTotal]; exact hTotalLt) (by rw [hcN]; omega)
      fun r hr => ?_
    rw [UInt64.le_iff_toNat_le, hNeed, hcN] at hFits
    replace hr : (r.toNat = 2 * capacityAt store p ∧
          8 * ((el.words (env.get x)).size + e.toNat + 1) ≤ 2 * capacityAt store p ∧
          2 * capacityAt store p ≤ 4294967296) ∨
        (r.toNat = 4294967296 ∧
          8 * ((el.words (env.get x)).size + e.toNat + 1) ≤ 2 * capacityAt store p ∧
          4294967296 < 2 * capacityAt store p) ∨
        (r.toNat = 8 * ((el.words (env.get x)).size + e.toNat + 1) ∧
          2 * capacityAt store p < 8 * ((el.words (env.get x)).size + e.toNat + 1)) := by
      rcases hr with h | h | h
      · left; omega
      · right; left; omega
      · right; right; omega
    have hRoomX : capacityAt store p < 8 * ((el.words (env.get x)).size + e.toNat + 1) := by
      omega
    have hr1 : 8 * ((UInt64.ofNat (el.words (env.get x)).size + e).toNat + 1) ≤ r.toNat := by
      rw [hTotal]; rcases hr with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have hr2 : r.toNat ≤ 4294967296 := by rcases hr with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have hRound := allocSize_round hr2 (by rw [hTotal] at hr1; omega)
    have hTopP := hOwned.below
    -- The allocation's charge fits whenever the growth's does; a request of `2 ^ 32` bytes
    -- follows a block too large for either.
    have hTrapA : TrapOK (!decide (heap.Within store m (allocCost (allocSize r).toNat))) Q :=
      hTrap.of_imp fun h => by
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h ⊢
        refine fun hw => h (hw.mono ?_)
        unfold Heap.Within at hw
        rw [hCost]
        rcases hr with hr | hr | hr
        · cases hp : paidAt paid x.index
          · have := room_alloc_unpaid (n := (el.words (env.get x)).size)
              (t := (el.words (env.get x)).size + e.toNat) hRound.1 hRound.2.1 hRound.2.2
              hRoomX (Or.inl ⟨hr.1, hr.2.1⟩)
            simp only [Bool.false_eq_true, ↓reduceIte, allocCost]; omega
          · have h1 := hPotX hOwnedX hDead hp
            have := room_alloc_paid (n := (el.words (env.get x)).size)
              (t := (el.words (env.get x)).size + e.toNat) hRound.1 hRound.2.1 hRound.2.2
              hRoomX (Or.inl ⟨hr.1, hr.2.1⟩)
            simp only [↓reduceIte, allocCost]; simp only [arrayPot] at h1; omega
        · exfalso
          have hH := room_huge (top := heap.top.toNat) (n := (el.words (env.get x)).size)
            (t := (el.words (env.get x)).size + e.toNat) hRoomX hCapacityP hr.2.2 (by omega)
          rw [hCost] at hw
          cases hp : paidAt paid x.index
          · simp only [hp, Bool.false_eq_true, ↓reduceIte, allocCost] at hw; omega
          · have h1 := hPotX hOwnedX hDead hp
            simp only [hp, ↓reduceIte, allocCost] at hw; simp only [arrayPot] at h1; omega
        · cases hp : paidAt paid x.index
          · have := room_alloc_unpaid (n := (el.words (env.get x)).size)
              (t := (el.words (env.get x)).size + e.toNat) hRound.1 hRound.2.1 hRound.2.2
              hRoomX (Or.inr hr)
            simp only [Bool.false_eq_true, ↓reduceIte, allocCost]; omega
          · have h1 := hPotX hOwnedX hDead hp
            have := room_alloc_paid (n := (el.words (env.get x)).size)
              (t := (el.words (env.get x)).size + e.toNat) hRound.1 hRound.2.1 hRound.2.2
              hRoomX (Or.inr hr)
            simp only [↓reduceIte, allocCost]; simp only [arrayPot] at h1; omega
    refine wpX_allocCopy (c := allocCost (allocSize r).toNat) hm hRt hAt (fun hs => (hAl hs).1) hPAl hCap le_rfl
      (hTrapA.imp fun _ h => h)
      hOwned.borrowed
      (by rw [hTotal]; exact hTotalLt) (by rw [hTotal]; omega) hr1 hr2 hP4 hT4 hN4
      (by show s.params.length ≤ b + 4; omega) (by rw [hp4, hl4]; omega)
      (by show s.params.length ≤ b + 5; omega) (by rw [hp4, hl4]; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      fun heap1 store1 s5 q words hSize hPrefix hStep1 hOwnedQ hShape hp5 hl5 hOther5 hQ5 hv5
        _ hAlq => ?_
    have hP5 : s5.get b = some (.i64 p) := by rw [hOther5 b (by omega) (by omega)]; exact hP4
    simp only [wpX_localGet_cons, hP5]
    obtain ⟨⟨hOwnedP1, hCapP1⟩, hApartPQ⟩ := hStep1.owned hOwned trivial
    refine wpX_release hm hRA hStep1.at_ (fun hs => (hAlq hs).2.2)
      (fun hs => ⟨hPAl hs, by rw [hCapP1]; exact hCapXAl hs⟩) hOwnedP1 fun hAlRel => ?_
    rw [wpX_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    have hRel := releaseStep hStep1.at_ hOwnedP1
    have hPQ : regionsDisjoint (block store1 q) (block store1 p) := by
      rw [block_eq hCapP1]
      exact regionsDisjoint_symm (hApartPQ _ (List.mem_singleton_self _))
    obtain ⟨⟨hOwnedQ2, hCapQ2⟩, -⟩ := hRel.owned hOwnedQ hPQ
    have hStepG := hStep1.transBoth hRel (keep := fun r => regionsDisjoint r (block store p))
      fun _ hr => ⟨trivial, fun _ => by rw [block_eq hCapP1]; exact hr⟩
    have aG := (a0.toWords.reframe hF4).replace (hStepG.mono (fun _ h => h) fun c hc => by
      rw [List.mem_singleton.mp hc, block_eq hCapQ2]
      exact List.mem_append_left _ (List.mem_singleton_self _)) hOwnedQ2
    have hF5 : Frame b s4 { s5 with values := s4.values } := ⟨hp5, hl5, fun j hj =>
      ⟨by show s5.get j = s4.get j; exact hOther5 j (by omega) (by omega),
        by show s5.get _ = s4.get _; exact hOther5 _ (by omega) (by omega)⟩,
      fun j hj => by show s5.get _ = s4.get _; exact hOther5 _ (by omega) (by omega)⟩
    -- The bound: the move's cost and the new block's potential, against `x`'s potential when it
    -- is paid.
    have hQAddr := hOwnedQ.address
    have hQBase := hOwnedQ.base
    have hr' : (r.toNat = 2 * capacityAt store p ∧
          8 * ((el.words (env.get x)).size + e.toNat + 1) ≤ 2 * capacityAt store p) ∨
        (r.toNat = 8 * ((el.words (env.get x)).size + e.toNat + 1) ∧
          2 * capacityAt store p < 8 * ((el.words (env.get x)).size + e.toNat + 1)) := by
      rcases hr with hr | hr | hr
      · exact Or.inl ⟨hr.1, hr.2.1⟩
      · exfalso
        have := hShape.le hr2
        omega
      · exact Or.inr hr
    exact hNext _ _ _ q words (by rw [hSize, hTotal]) hPrefix (aG.reframe hF5)
      (by show s5.get (b + 1) = _; rw [hOther5 _ (by omega) (by omega)]; exact hN4) hQ5 rfl
      (fun hs => ⟨hAlRel hs, Ty.AlignedVal.ownedArray (hAlq hs).1 (by rw [hCapQ2]; exact (hAlq hs).2.1)⟩) (by
        rw [ite_eq_left ⟨hOwnedX, hDead⟩, hCost]
        show heap1.top.toNat + arrayPot _ q words.size ≤ _
        simp only [arrayPot, hCapQ2, hSize, hTotal]
        cases hp : paidAt paid x.index
        · have := room_move_unpaid (top := heap.top.toNat) (top' := heap1.top.toNat)
            (n := (el.words (env.get x)).size) (t := (el.words (env.get x)).size + e.toNat)
            hRound.1 hRound.2.1 hRound.2.2 hCapacityP hRoomX hr' hShape
          simp only [Bool.false_eq_true, ↓reduceIte, allocCost]; omega
        · have h1 := hPotX hOwnedX hDead hp
          have := room_move_paid (top := heap.top.toNat) (top' := heap1.top.toNat)
            (n := (el.words (env.get x)).size) (t := (el.words (env.get x)).size + e.toNat)
            hRound.1 hRound.2.1 hRound.2.2 hCapacityP hRoomX hr' hShape
          simp only [↓reduceIte, allocCost]; simp only [arrayPot] at h1; omega)

/-- `Var.roomCode`: an owned array, at the address in local `b + 4`, whose first elements are
those of `x`, whose length is `x`'s length plus the word `e` in local `ext`, and whose block has
room for that length.  An owned `x` that dies is consumed, and any other `x` is read.  The code
traps only when `top` cannot rise by the potential of the paid owned variables that die plus
`Var.roomCost` within the cap.  `top` after the code, plus the potential of the array when `x` is
owned and dies, is at most `top` before it plus that sum. -/
theorem spec_room (hm : Runtime m) {Γ' : List Ty} {el : Elem} (x : Var Γ' (.array el))
    {env : Env Γ'}
    {slots : List Slot} {paid : List Bool} {live : Nat → Bool} {b ext : Nat} {e : UInt64}
    {heap : Heap}
    {store : Store Unit} {s : Locals} {rest : Program} {Q : Assertion Unit}
    (hVars : Holds env slots (fun i => live i || i == x.index) b heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ b)
    (hRoom : b + 6 ≤ s.positions) (hExt : s.get ext = some (.i64 e))
    (hExtB : ext < b) (he : e.toNat ≤ 536870912)
    (hTrap : TrapOK (!decide (heap.Within store m
      (dyingPot store s env slots paid (fun i => live i || i == x.index) live +
        x.roomCost (slots.map Slot.mode) paid live (env.get x) e.toNat))) Q)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (q : UInt64)
      (words : Array UInt64), words.size = (el.words (env.get x)).size + e.toNat →
      (∀ j (hj : j < (el.words (env.get x)).size), words[j]! = (el.words (env.get x))[j]) →
      After env slots (fun i => live i || i == x.index) live b heap store s (.array .word) .owned
        words heap' store' s' [.i64 q] →
      s'.get (b + 1) = some (.i64 (UInt64.ofNat (el.words (env.get x)).size)) →
      s'.get (b + 4) = some (.i64 q) → s'.values = s.values →
      heap'.top.toNat +
          (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
            arrayPot store' q words.size else 0) ≤
        heap.top.toNat + dyingPot store s env slots paid (fun i => live i || i == x.index) live +
          x.roomCost (slots.map Slot.mode) paid live (env.get x) e.toNat →
      wp m rest Q store' s' host) :
    wp m (x.roomCode slots b live ext ++ rest) Q store s host :=
  specX_room (strict := false) hm nofun nofun x hVars hAt nofun hCap hBase hRoom hExt hExtB he hTrap
    (fun heap' store' s' q words a1 a2 a3 a4 a5 a6 _ a8 => hNext heap' store' s' q words a1 a2 a3 a4 a5 a6 a8)

/-- `x.push v`: the value's words from local `base` on, the array taken with room for one more
element by `Var.roomCode` from local `base + k + 1` on, and the writes of the element's words
after the array's words. -/
theorem specX_push (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (hRt : strict = true → AllocAligned m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {v : Expr S Γ' (.elem e)}
    (vSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv v env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.push x v) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hv := Nat.le_max_left v.width (e.width + 7)
  have h8 := Nat.le_max_right v.width (e.width + 7)
  have hk := e.width_pos
  simp only [Expr.placeArgs] at hPlace
  have hT : (Expr.push x v).allocs funs flags bounds (slots.map Slot.mode) paid live env =
      v.allocs funs flags bounds (slots.map Slot.mode) paid (fun j => live j || j == x.index) env +
        x.roomCost (slots.map Slot.mode) paid live (env.get x) (wordCount e.width).toNat := rfl
  have hdS : (Expr.push x v).fits funs fits env = true → v.fits funs fits env = true :=
    fun hd => by simpa [Expr.fits] using hd
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The value's words, from local `base` on.
  have hIn : ∀ k, ((live k || k == x.index) || v.uses k) = true →
      (live k || (Expr.push x v).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact live_assoc _ _ _ h
  -- The variables that die in the value, and the array when it dies.
  have hDiv : dyingPot store s env slots paid (fun k => live k || (Expr.push x v).uses k) live =
      dyingPot store s env slots paid (fun k => (live k || k == x.index) || v.uses k)
        (fun k => live k || k == x.index) +
      dyingPot store s env slots paid (fun k => live k || k == x.index) live := by
    rw [dyingPot_congr (L0 := fun k => live k || (Expr.push x v).uses k)
        (L0' := fun k => (live k || k == x.index) || v.uses k)
        (fun k => by simp only [Expr.uses, Bool.or_assoc]) fun _ => rfl]
    exact dyingPot_split _ _ _ (fun k h => by simp [h]) (fun k h => by simp [h])
  refine vSpec env slots paid _ h base heap store s hh hpv
    (hVars.live_mono hIn) hAt (fun hs => (hAl hs).live_mono hIn) (hSafe.mono hIn) hCap hBase (by omega) hPlace _ _
    (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun _ => by simp [Expr.aborts])
      fun _ hw => hw.mono (by rw [hT, hDiv]; omega))
    fun heap1 store1 s1 ws1 a1 hAlV hTopV => ?_
  replace hTopV : v.fits funs fits env = true →
      heap1.top.toNat ≤ heap.top.toNat + dyingPot store s env slots paid
        (fun k => (live k || k == x.index) || v.uses k) (fun k => live k || k == x.index) +
        v.allocs funs flags bounds (slots.map Slot.mode) paid (fun j => live j || j == x.index) env :=
    fun hd => Nat.le_trans (Nat.le_add_right _ _) (hTopV hd)
  have hR1 := Ty.rep_elem.mp a1.rep
  subst hR1
  have e1a := a1.toEvolves rfl
  have hp1a : s1.params = s.params := e1a.frame.params
  have hh1a : s1.positions = h := e1a.frame.positions.trans hh
  refine wpX_storeCode (e.values (v.denote funs env)) h base e.types s1 s.values
    (by rw [e.values_length, e.types_length]) hh1a (by rw [hp1a]; omega)
    (by rw [e.types_length, hh1a]; omega) fun s1' f1 hold1 _ => ?_
  have f1' : Frame base s1 { s1' with values := s.values } := f1.trans Frame.ofValues
  have e1 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) base heap store s heap1 store1
      { s1' with values := s.values } :=
    ⟨e1a.step, e1a.frame.trans f1', e1a.holds.agree f1'⟩
  have hp1 : s1'.params = s.params := f1.params.trans hp1a
  have hh1 : s1'.positions = h := f1.positions.trans hh1a
  -- The count of new words, in local `base + k`.
  simp only [wpX_constI64_cons]
  have hLowK : ({ s1' with values := s.values } : Locals).params.length ≤ base + e.width := by
    show s1'.params.length ≤ _; rw [hp1]; omega
  have hHighK' : base + e.width < ({ s1' with values := s.values } : Locals).positions := by
    simp only [Locals.positions_values, hh1]; omega
  have hHighK := Locals.lt_total hHighK'
  refine wpX_localSet_local hLowK hHighK ?_
  set s2 := setLocal { s1' with values := s.values } (base + e.width) (.i64 (wordCount e.width))
    with hs2
  have hK2 : s2.get (base + e.width) = some (.i64 (wordCount e.width)) :=
    Locals.get_setLocal_same hLowK hHighK
  have hF2 : Frame (base + e.width) { s1' with values := s.values } s2 :=
    Frame.setValues (s := { s1' with values := s.values }) (vs := s.values) hLowK le_rfl hHighK'
  have hold2 : LocalsHold s2 base e.types (e.values (v.denote funs env)) :=
    (LocalsHold.frame (Frame.ofValues.trans hF2) (by rw [e.values_length, e.types_length])
      (by rw [e.types_length])).mpr hold1
  have e2 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) base heap store s heap1 store1 s2 :=
    ⟨e1.step, e1.frame.trans (hF2.mono (by omega)), e1.holds.agree (hF2.mono (by omega))⟩
  have hp2 : s2.params = s.params := e2.frame.params
  have hh2 : s2.positions = h := e2.frame.positions.trans hh
  have hDx : dyingPot store1 s2 env slots paid (fun k => live k || k == x.index) live =
      dyingPot store s env slots paid (fun k => live k || k == x.index) live :=
    dyingPot_evolves (hVars.live_mono hIn) e2 (fun k h => by simp [h]) _ _ fun _ h => h
  -- The array, with room for one more element, from local `base + k + 1` on.
  refine specX_room hm hRA hRt x (paid := paid) (b := base + e.width + 1) (ext := base + e.width)
      (e := wordCount e.width)
    (s := s2) (e2.holds.mono (by omega))
    e2.step.at_
    (fun hs => HoldsA.evolves (hVars.live_mono hIn) ((hAl hs).live_mono hIn) e2
      (fun k h => by simp [h]) (hAlV hs).1.1) (by rw [e2.step.cap m]; exact hCap) (by rw [hp2]; omega)
    (by rw [hh2]; omega) hK2 (by omega) (by rw [wordCount_toNat]; omega)
    (hTrap.alloc (by simp [Expr.aborts]) fun hd hw => hw.of_le
      (by have := hTopV (hdS (fits_of_not hd)); rw [hDx]; rw [hT, hDiv] at hw; omega)
      (e2.step.cap m))
    fun heap2 store2 s3 q words hSize hPrefix aR hN3 hQ3 hv3 hAlR hTopR => ?_
  obtain ⟨p, hp, hOwnedQ⟩ := aR.rep
  replace hOwnedQ : heap2.Owned store2 p words := hOwnedQ
  obtain rfl : p = q := by simp only [List.cons.injEq, Value.i64.injEq] at hp; exact hp.1.symm
  have hQAl : strict = true → p.toNat % 8 = 0 := fun hs =>
    Ty.AlignedVal.ownedPtr (by have := hOwnedQ.base; omega) (hAlR hs).2
  have hFitQ := hOwnedQ.values.1
  have hkw : (wordCount e.width).toNat = e.width := by
    rw [wordCount_toNat] at hSize ⊢; omega
  rw [hkw, Elem.words_size] at hSize
  have hL64 : (UInt64.ofNat (e.words (env.get x)).size).toNat = (env.get x).size * e.width := by
    rw [Elem.words_size]
    exact UInt64.toNat_ofNat_of_lt'
      (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hold3 : LocalsHold s3 base e.types
      (List.zipWith typedValue e.types (e.toWords (v.denote funs env))) := by
    rw [e.values_typed]
    exact (LocalsHold.frame (aR.frame.mono (base := base + e.width) (by omega))
      (by rw [e.values_length, e.types_length]) (by rw [e.types_length])).mpr hold2
  -- The writes of the element's words after the array's words.
  refine wpX_storeWordsCode hQAl 0 base e.types (e.toWords (v.denote funs env)) words store2 s3 aR
    (aR.frame.positions.trans hh2) hQ3 hN3 hold3 (by rw [e.toWords_length, e.types_length]) (e.typed_words _)
    (by rw [hL64, e.types_length, hSize]; omega) fun store4 a4 hCap4 => ?_
  rw [hL64] at a4
  simp only [Nat.add_zero] at a4
  rw [Elem.words_push_into e (v.denote funs env) hSize (fun w hw => by
    rw [getElem!_pos (e.words (env.get x)) w (by rw [Elem.words_size]; exact hw)]
    exact hPrefix w (by rw [Elem.words_size]; exact hw))] at a4
  have aFin := After.prepend (hVars.live_mono hIn) e2 ((After.ofWords a4).lower e2.holds (by omega)
    fun k h => by simp [h]) (fun k h => by simp [h]) fun k h => by simp [h]
  simp only [wpX_localGet_cons, hQ3]
  have hBound : (Expr.push x v).fits funs fits env = true →
      heap2.top.toNat + (if (Expr.push x v).paid flags (slots.map Slot.mode) paid live then
          (Ty.array e).pot store4 [.i64 p] ((Expr.push x v).denote funs env) else 0) ≤
        heap.top.toNat + dyingPot store s env slots paid (fun i => live i || (Expr.push x v).uses i)
          live + (Expr.push x v).allocs funs flags bounds (slots.map Slot.mode) paid live env := by
    intro hd
    have hV := hTopV (hdS hd)
    rw [hDx] at hTopR
    have hWords : (e.words ((env.get x).push (v.denote funs env))).size = words.size := by
      rw [Elem.words_size, Array.size_push, hSize, Nat.succ_mul]
    have hPot : (Ty.array e).pot store4 [.i64 p] ((Expr.push x v).denote funs env) =
        arrayPot store2 p words.size := by
      show arrayPot store4 p (e.words ((env.get x).push (v.denote funs env))).size = _
      rw [hWords]; unfold arrayPot; rw [hCap4]
    rw [hT, hDiv]
    show heap2.top.toNat + (if (modeAt (slots.map Slot.mode) x.index == .owned &&
        !live x.index) = true then _ else 0) ≤ _
    rw [hPot]
    by_cases hc : (slots.getD x.index default).mode = .owned ∧ live x.index = false
    · rw [ite_eq_left hc] at hTopR
      rw [ite_eq_left
          (by simp only [modeAt, Slot.modes_getD, hc.1, hc.2, beq_self_eq_true, Bool.not_false,
        Bool.and_self])]
      omega
    · rw [ite_eq_right hc] at hTopR
      rw [ite_eq_right (by
        simp only [modeAt, Slot.modes_getD, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
        exact hc)]
      omega
  simpa [hv3, hs2, setLocal] using hNext heap2 store4 s3 [.i64 p] (aFin.liveIn hIn)
    (fun hs => ⟨HoldsA.after hVars (hAl hs) (aFin.liveIn hIn) (fun k h => by simp [h]) (hAlR hs).1,
      Ty.AlignedVal.ownedArray (hQAl hs) (by rw [hCap4]; exact Ty.AlignedVal.arrayCap (hAlR hs).2)⟩)
    hBound

/-- `x.push v`: the value's words from local `base` on, the array taken with room for one more
element by `Var.roomCode` from local `base + k + 1` on, and the writes of the element's words
after the array's words. -/
theorem spec_push (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {v : Expr S Γ' (.elem e)}
    (vSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv v env slots paid live) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.push x v) env
        slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_push (strict := false) hm nofun nofun x
      (fun env slots paid live => CodeSpecX.false_iff.mpr (vSpec env slots paid live)) env slots
      paid live)

/-- `x ++ y`: the length of `y` in local `base`, the array `x` taken with room for `y`'s elements
by `Var.roomCode` from local `base + 1` on, with `y` live, the copy of `y`'s elements after `x`'s,
and the release of `y` when it is owned and dies there. -/
theorem specX_append (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (hRt : strict = true → AllocAligned m) {Γ' : List Ty} {e : Elem} (x y : Var Γ' (.array e)) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.append (S := S) x y) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom _
      rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hT : (Expr.append (S := S) x y).allocs funs flags bounds (slots.map Slot.mode) paid live env =
      x.roomCost (slots.map Slot.mode) paid (fun k => live k || k == y.index) (env.get x)
        ((env.get y).size * e.width) := rfl
  have hTot : 2 * s.positions ≤ s.params.length + s.locals.length := by
    simp only [Locals.positions]; omega
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The length of `y`, in local `base`.
  obtain ⟨hBelowY, wy, holdy, hRepY⟩ := hVars.get y (by simp [Expr.uses])
  obtain ⟨py, rfl, hArrY⟩ := hRepY
  have hPYAl : strict = true → py.toNat % 8 = 0 := fun hs =>
    Ty.AlignedVal.array hArrY ((hAl hs).2 _ y (by simp [Expr.uses]) [.i64 py] holdy rfl)
  have hYB : (slots.getD y.index default).loc < base := by
    have := hBelowY; simp only [Ty.width] at this; omega
  have hBY := hArrY.borrow
  have hAY := hBY.values
  have hLenY := hAY.lengthBound
  have hFitY := hAY.1
  have hmY : (e.words (env.get y)).size < 536870912 := by omega
  have hMY : (UInt64.ofNat (e.words (env.get y)).size).toNat = (e.words (env.get y)).size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hExt : (UInt64.ofNat (e.words (env.get y)).size).toNat = (env.get y).size * e.width := by
    rw [hMY, Elem.words_size]
  have hPY : s.get (slots.getD y.index default).loc = some (.i64 py) := by
    exact LocalsHold.word holdy
  simp only [wpX_localGet_cons, hPY, wpX_wrapI64_cons, wpX_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hAY.lengthRead]
  refine ⟨fun hs => UInt64.toUInt32_mod8 (hPYAl hs), ?_⟩
  refine wpX_localSet_local hBase (by omega) ?_
  have hLow0 : ({ s with values := s.values } : Locals).params.length ≤ base := hBase
  set s1 := setLocal { s with values := s.values } base
    (.i64 (UInt64.ofNat (e.words (env.get y)).size))
    with hs1
  have hM1 : s1.get base = some (.i64 (UInt64.ofNat (e.words (env.get y)).size)) :=
    Locals.get_setLocal_same hLow0 (by omega)
  have hF1 : Frame base s s1 := by
    rw [hs1]; exact Frame.setValues hLow0 le_rfl (by rw [hh]; omega)
  have hh1' : s1.positions = s.positions := hF1.positions
  -- The array `x` with room, from local `base + 1` on, with `y` live.
  have hIn : ∀ k, ((live k || k == y.index) || k == x.index) = true →
      (live k || (Expr.append (S := S) x y).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact append_live _ _ _ h
  have hVars1 : Holds env slots (fun k => (live k || k == y.index) || k == x.index) (base + 1)
      heap store s1 :=
    ((hVars.live_mono hIn).agree hF1).mono (by omega)
  have e0 : Evolves env slots (fun i => live i || (Expr.append (S := S) x y).uses i)
      (fun k => (live k || k == y.index) || k == x.index) base heap store s heap store s1 :=
    ⟨Step.refl hAt _, hF1, (hVars.live_mono hIn).agree hF1⟩
  -- The potential of `x` when it is paid and dies, which `spec_room` counts.
  have hDx : dyingPot store s1 env slots paid (fun k => (live k || k == y.index) || k == x.index)
        (fun k => live k || k == y.index) ≤
      dyingPot store s env slots paid (fun i => live i || (Expr.append (S := S) x y).uses i)
        live := by
    rw [dyingPot_evolves hVars e0 hIn _ _ fun _ h => h]
    exact dyingPot_mono (fun k h => hIn k h) fun k h => by simp [h]
  refine specX_room hm hRA hRt x (paid := paid) (b := base + 1) (ext := base)
      (e := UInt64.ofNat (e.words (env.get y)).size)
    (s := s1) hVars1 hAt
    (fun hs => HoldsA.agree (hVars.live_mono hIn) ((hAl hs).live_mono hIn) hF1) hCap (by show s.params.length ≤ base + 1; omega)
    (by rw [hh1', hh]; omega)
    hM1 (by omega) (by rw [hMY]; exact Nat.le_of_lt hmY)
    (hTrap.alloc (by simp [Expr.aborts]) fun _ hw => hw.mono (by have := hDx; rw [hT, hExt]; omega))
    fun heap1 store1 s2 q words hSize hPrefix aR hN2 hQ2 hv2 hAlR hTopR => ?_
  rw [hMY] at hSize
  have hp2 : s2.params = s.params := aR.frame.params
  have hl2 : s2.locals.length = s.locals.length := by rw [aR.frame.length]; simp [s1, setLocal]
  have hM2 : s2.get base = some (.i64 (UInt64.ofNat (e.words (env.get y)).size)) :=
    (aR.frame.below base (by omega)).1.trans hM1
  have hh2' : s2.positions = s.positions := aR.frame.positions.trans hh1'
  -- `y` stays readable, apart from the new array.
  obtain ⟨-, wy', holdy', hRepY'⟩ := aR.holds.get y (by simp)
  have hAgree2 : ∀ j < base, s2.get j = s.get j := fun j hj =>
    (aR.frame.below j (by omega)).1.trans (hF1.below j hj).1
  have holdy2 : LocalsHold s2 (slots.getD y.index default).loc (Ty.array e).types [.i64 py] :=
    (LocalsHold.frame (hF1.trans (aR.frame.mono (base := base) (by omega))) rfl
      (by simp only [Ty.types, List.length_singleton]; omega)).mpr holdy
  obtain rfl := LocalsHold.unique holdy' holdy2 (by rw [hRepY'.length]; rfl)
  obtain ⟨py', hpy, hArrY1⟩ := hRepY'
  obtain rfl : py = py' := by simp only [List.cons.injEq, Value.i64.injEq] at hpy; exact hpy.1
  have hBY1 := hArrY1.borrow
  obtain ⟨p, hp, hOwnedQ⟩ := aR.rep
  replace hOwnedQ : heap1.Owned store1 p words := hOwnedQ
  obtain rfl : p = q := by simp only [List.cons.injEq, Value.i64.injEq] at hp; exact hp.1.symm
  have hQAl : strict = true → p.toNat % 8 = 0 := fun hs =>
    Ty.AlignedVal.ownedPtr (by have := hOwnedQ.base; omega) (hAlR hs).2
  have hCapQ := hOwnedQ.capacity
  have hBaseQ := hOwnedQ.base
  have hApartQY : py.toNat + 8 * ((e.words (env.get y)).size + 1) ≤ p.toNat ∨
      p.toNat + 8 * (words.size + 1) ≤ py.toNat := by
    have hD := aR.apart _ y (by simp) (Or.inl rfl) [.i64 py] holdy2 rfl (block store1 p)
      (List.mem_singleton_self _)
    cases hmy : (slots.getD y.index default).mode
    · rw [hmy] at hD
      have := hD _ (List.mem_singleton_self _)
      simp only [block, regionsDisjoint] at this
      omega
    · rw [hmy] at hD hArrY1
      have hOwnedY : heap1.Owned store1 py (e.words (env.get y)) := hArrY1
      have := hD (block store1 py) (List.mem_singleton_self _)
      have := hOwnedY.capacity
      have := hOwnedY.base
      simp only [block, regionsDisjoint] at *
      omega
  -- The address of element `n` of the new array, in local `base + 4`.
  have h8n : UInt64.ofNat (e.words (env.get x)).size * 8 =
      UInt64.ofNat (8 * (e.words (env.get x)).size) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  simp only [wpX_localGet_cons, Locals.get_values, hQ2, hN2, wpX_constI64_cons, wpX_mulI64_cons,
    wpX_addI64_cons, h8n]
  have hLow2 : ({ s2 with values := s2.values } : Locals).params.length ≤ base + 4 := by
    show s2.params.length ≤ base + 4; rw [hp2]; omega
  have hHigh2 : base + 4 < ({ s2 with values := s2.values } : Locals).params.length +
      ({ s2 with values := s2.values } : Locals).locals.length := by
    show base + 4 < s2.params.length + s2.locals.length; rw [hp2, hl2]; omega
  refine wpX_localSet_local hLow2 hHigh2 ?_
  set s3 := setLocal { s2 with values := s2.values } (base + 4)
    (.i64 (p + UInt64.ofNat (8 * (e.words (env.get x)).size))) with hs3
  have hD3 : s3.get (base + 4) = some (.i64 (p + UInt64.ofNat (8 * (e.words (env.get x)).size))) :=
    Locals.get_setLocal_same hLow2 hHigh2
  have hGet3 : ∀ j, j ≠ base + 4 → s3.get j = s2.get j := fun j hj => by
    rw [hs3, Locals.get_setLocal_ne hLow2 hj, Locals.get_values]
  have hp3 : s3.params = s.params := hp2
  have hl3 : s3.locals.length = s.locals.length := by simp [s3, setLocal, hl2]
  -- The copy of `y`'s elements after `x`'s.
  refine wpX_copyInto (k := (e.words (env.get x)).size) (fun hs => ⟨hPYAl hs, hQAl hs⟩) hBY1.values hOwnedQ.values (by omega)
    hApartQY
    (by rw [hGet3 _ (by omega), hAgree2 _ hYB]; exact hPY) hD3
    (by rw [hGet3 _ (by omega)]; exact hM2) (by omega) (by omega)
    (by omega) (by rw [hp3]; omega) (by rw [hp3, hl3]; omega)
    fun store2 s4 hW hA2 hp4 hl4 hOther4 hv4 => ?_
  have hWords : overlay words (e.words (env.get y)) (e.words (env.get x)).size
      (e.words (env.get y)).size = e.words (env.get x ++ env.get y) := by
    rw [Elem.words_append]
    apply Array.ext (by simp [overlay_size, hSize]) fun j h1 h2 => ?_
    simp only [overlay, Array.getElem_ofFn]
    rw [overlay_size] at h1
    by_cases hj : j < (e.words (env.get x)).size
    · rw [ite_eq_right (by omega), Array.getElem_append_left hj, ← hPrefix j hj,
        getElem!_pos words j h1]
    · rw [ite_eq_left (by omega), Array.getElem_append_right (by omega),
        getElem!_pos _ _ (by omega)]
  rw [hWords] at hA2
  have hWithin : WritesWithin store1 store2 p.toNat (capacityAt store1 p) :=
    ⟨by rw [hW.1], hW.2.1, fun a ha => hW.2.2 a (by omega)⟩
  have aW := aR.rewrite hWithin (by rw [hW.1]) hA2
    (by rw [Elem.words_append, Array.size_append]; omega)
  have hCap2 : capacityAt store2 p = capacityAt store1 p :=
    (hOwnedQ.rewrite hWithin hA2 (by rw [Elem.words_append, Array.size_append]; omega)).2
  have hF4 : Frame (base + 1) s2 s4 := ⟨hp4.trans rfl, by rw [hl4]; simp [s3, setLocal],
    fun j hj => ⟨by rw [hOther4 j (by omega), hGet3 j (by omega)],
      by rw [hOther4 _ (by omega), hGet3 _ (by omega)]⟩,
    fun j hj => by rw [hOther4 _ (by omega), hGet3 _ (by omega)]⟩
  -- The release of `y` when it is owned and dies here.
  refine After.releaseX hm hRA (s1 := s4) (live := live)
    (sel := fun k => k == y.index && !live k) hVars1 (After.ofWords (aW.reframe hF4))
    (fun hs => ⟨HoldsA.after hVars1 (HoldsA.agree (hVars.live_mono hIn) ((hAl hs).live_mono hIn) hF1)
      (After.ofWords (aW.reframe hF4)) (fun k h => by simp [h]) (hAlR hs).1,
      Ty.AlignedVal.ownedArray (hQAl hs) (by rw [hCap2]; exact Ty.AlignedVal.arrayCap (hAlR hs).2)⟩)
    (fun k h => by simp [h]) (fun k h => by
      simp only [Bool.and_eq_true, beq_iff_eq] at h; simp [h.1])
    (fun k h => by simp [h]) fun heap2 store3 a' hTop2 hRegions hAl' => ?_
  have hQ4 : s4.get (base + 5) = some (.i64 p) := by
    rw [hOther4 _ (by omega), hGet3 _ (by omega)]; exact hQ2
  simp only [wpX_localGet_cons, hQ4]
  have aFin := After.prepend hVars e0 (a'.lower ((hVars.live_mono hIn).agree
    hF1) (by omega) fun k h => by simp [h]) hIn fun k h => by simp [h]
  have hv3 : s3.values = s.values := by rw [hs3]; exact hv2
  have hBound : (Expr.append (S := S) x y).fits funs fits env = true →
      heap2.top.toNat + (if (Expr.append (S := S) x y).paid flags (slots.map Slot.mode) paid live then
          (Ty.array e).pot store3 [.i64 p] ((Expr.append (S := S) x y).denote funs env) else 0) ≤
        heap.top.toNat + dyingPot store s env slots paid
          (fun i => live i || (Expr.append (S := S) x y).uses i) live +
          (Expr.append (S := S) x y).allocs funs flags bounds (slots.map Slot.mode) paid live env := by
    intro _
    have hPot : (Ty.array e).pot store3 [.i64 p] ((Expr.append (S := S) x y).denote funs env) =
        arrayPot store1 p words.size := by
      show (Ty.array e).pot store3 [.i64 p] (env.get x ++ env.get y) = _
      rw [Ty.pot_of_blocks _ _ _ hRegions]
      show arrayPot store2 p (e.words (env.get x ++ env.get y)).size = _
      rw [Elem.words_append, Array.size_append, ← hSize]; unfold arrayPot; rw [hCap2]
    rw [hTop2, hT, ← hExt, hPot]
    show heap1.top.toNat + (if (modeAt (slots.map Slot.mode) x.index == .owned &&
        !(live x.index || x.index == y.index)) = true then _ else 0) ≤ _
    by_cases hc : (slots.getD x.index default).mode = .owned ∧
        (live x.index || x.index == y.index) = false
    · rw [ite_eq_left hc] at hTopR
      rw [ite_eq_left
          (by simp only [modeAt, Slot.modes_getD, hc.1, hc.2, beq_self_eq_true, Bool.not_false,
        Bool.and_self])]
      omega
    · rw [ite_eq_right hc] at hTopR
      rw [ite_eq_right (by
        simp only [modeAt, Slot.modes_getD, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
        exact hc)]
      omega
  simpa [hv4, hv3] using hNext heap2 store3 s4 [.i64 p] aFin hAl' hBound

/-- `x ++ y`: the length of `y` in local `base`, the array `x` taken with room for `y`'s elements
by `Var.roomCode` from local `base + 1` on, with `y` live, the copy of `y`'s elements after `x`'s,
and the release of `y` when it is owned and dies there. -/
theorem spec_append (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x y : Var Γ' (.array e)) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.append (S := S) x y) env
        slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_append (strict := false) hm nofun nofun x y env slots paid live)

/-- `LeanExe.eraseAt x i`: the position in local `base`, the array as owned in local `base + 1`,
its length in local `base + 2`, and, when the position is below the size, the element's first
word in local `base + 3`, the move of the words after the element down by its word count, and the
write of the shorter length. -/
theorem specX_eraseAt (hCopy : CopyCodeX strict m host) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word}
    (iSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv i env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.eraseAt x i) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi := Nat.le_max_left i.width 8
  have hx := Nat.le_max_right i.width 8
  have hk := e.width_pos
  have hcw : copyWidth (Ty.array e) = 4 := rfl
  simp only [Expr.placeArgs] at hPlace
  have hT : (Expr.eraseAt x i).allocs funs flags bounds (slots.map Slot.mode) paid live env =
      i.allocs funs flags bounds (slots.map Slot.mode) paid (fun j => live j || j == x.index) env +
        x.ownedCost (slots.map Slot.mode) live (env.get x) := rfl
  have hdS : (Expr.eraseAt x i).fits funs fits env = true → i.fits funs fits env = true :=
    fun hd => by simpa [Expr.fits] using hd
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  -- The position, in local `base`.
  have hIn : ∀ k, ((live k || k == x.index) || i.uses k) = true →
      (live k || (Expr.eraseAt x i).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact live_assoc _ _ _ h
  have hDi : dyingPot store s env slots paid (fun k => (live k || k == x.index) || i.uses k)
        (fun k => live k || k == x.index) ≤
      dyingPot store s env slots paid (fun k => live k || (Expr.eraseAt x i).uses k) live :=
    dyingPot_mono hIn fun k h => by simp [h]
  refine iSpec env slots paid _ h base heap store s hh hpv
    (hVars.live_mono hIn) hAt (fun hs => (hAl hs).live_mono hIn) (hSafe.mono hIn) hCap hBase (by omega) hPlace _ _
    (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun _ => by simp [Expr.aborts])
      fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hAlI hTopI => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  refine After.storeWordX a1 le_rfl hBase (by rw [hh]; omega) fun e1 hI1 => ?_
  have hp1 := e1.frame.params
  have hh1 := e1.frame.positions.trans hh
  -- The array as owned, in local `base + 1`.
  refine specX_ownedVar hCopy x hh1 (hp1.trans hpv) (e1.holds.mono (Nat.le_succ base)) e1.step.at_
    (fun hs => HoldsA.evolves (hVars.live_mono hIn) ((hAl hs).live_mono hIn) e1
      (fun k h => by simp [h]) (hAlI hs).1.1)
    ((hSafe.mono hIn).evolves (hVars.live_mono hIn) e1 (fun k hk => by simp [hk]))
    (by rw [e1.step.cap m]; exact hCap) (by rw [hp1]; omega) (by omega)
    (hTrap.alloc (by simp [Expr.aborts]) fun hd hw => hw.of_le
      (by have := hTopI (hdS (fits_of_not hd)); rw [hT]; omega) (e1.step.cap m))
    fun heap3 store3 s3 ws3 a3 hAlO hTopO => ?_
  obtain ⟨p, hws, hOwned⟩ := a3.rep
  subst hws
  have hPAl : strict = true → p.toNat % 8 = 0 := fun hs => Ty.AlignedVal.array hOwned (hAlO hs).2
  have hp3 : s3.params = s.params := a3.frame.params.trans hp1
  have hh3 : s3.positions = h := a3.frame.positions.trans hh1
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow3 : ({ s3 with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s3.params.length ≤ _; rw [hp3]; omega
  have hHigh3' : base + 1 < s3.positions := by rw [hh3]; omega
  have hHigh3 := Locals.lt_total (s := { s3 with values := s.values }) hHigh3'
  refine wpX_localSet_local hLow3 hHigh3 ?_
  set s4 : Locals := setLocal { s3 with values := s.values } (base + 1) (.i64 p) with hs4
  have hP4 : s4.get (base + 1) = some (.i64 p) := Locals.get_setLocal_same hLow3 hHigh3
  have hF4 : Frame (base + 1) s3 s4 := Frame.setValues hLow3 le_rfl hHigh3'
  have hI4 : s4.get base = some (.i64 (i.denote funs env)) :=
    (hF4.below base (by omega)).1.trans ((a3.frame.below base (by omega)).1.trans hI1)
  have hh4 : s4.positions = h := hF4.positions.trans hh3
  have hp4 : s4.params = s.params := hF4.params.trans hp3
  have a4 := a3.toWords.reframe hF4
  -- The rest of the code, from the array after the move or without it.
  have hFinish : ∀ (store4 : Store Unit) (s' : Locals) (ws : Array UInt64),
      Frame (base + 1) s4 s' → s'.values = s.values →
      ws = e.words (LeanExe.eraseAt (env.get x) (i.denote funs env)) →
      After env slots (fun k => live k || k == x.index) live (base + 1) heap1 store1
        (setLocal { s1 with values := s.values } base (.i64 (i.denote funs env)))
        (.array .word) .owned ws heap3 store4 s' [.i64 p] →
      (strict = true → heap3.Aligned ∧ Ty.AlignedVal .owned store4 (.array .word) [.i64 p] ws) →
      wpX strict m rest Q store4 { s' with values := .i64 p :: s'.values } host := by
    rintro store4 s' ws _ hv' rfl aX hAlX
    have aX1 := (After.ofWords aX).lower e1.holds (Nat.le_succ base) fun k h => by simp [h]
    have aX2 := After.prepend (hVars.live_mono hIn) e1 aX1 (fun k h => by simp [h])
      fun k h => by simp [h]
    simpa [hv'] using hNext heap3 store4 _ [.i64 p] (aX2.liveIn hIn)
      (fun hs => ⟨HoldsA.after hVars (hAl hs) (aX2.liveIn hIn) (fun k h => by simp [h]) (hAlX hs).1,
        Ty.AlignedVal.ownedArray (hPAl hs) (Ty.AlignedVal.arrayCap (hAlX hs).2)⟩) fun hd => top_unpaid rfl (by
      have := hTopI (hdS hd); rw [hT]; omega)
  have hA := hOwned.values
  have hLength := hA.lengthBound
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  have hn64 : (env.get x).size < UInt64.size := by
    have := Nat.le_mul_of_pos_right (env.get x).size hk
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega
  -- The length, in local `base + 2`.
  show wpX strict m _ Q store3 s4 host
  simp only [wpX_localGet_cons, hP4, wpX_wrapI64_cons, wpX_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size]
  refine ⟨fun hs => UInt64.toUInt32_mod8 (hPAl hs), ?_⟩
  have hLow5 : ({ s4 with values := s4.values } : Locals).params.length ≤ base + 2 := by
    show s4.params.length ≤ _; rw [hp4]; omega
  have hHigh5' : base + 2 < s4.positions := by rw [hh4]; omega
  have hHigh5 := Locals.lt_total (s := { s4 with values := s4.values }) hHigh5'
  refine wpX_localSet_local hLow5 hHigh5 ?_
  set L := (env.get x).size * e.width with hLdef
  set s5 : Locals := setLocal { s4 with values := s4.values } (base + 2) (.i64 (UInt64.ofNat L))
    with hs5
  have hF5 : Frame (base + 2) s4 s5 := Frame.setValues hLow5 le_rfl hHigh5'
  have hL5 : s5.get (base + 2) = some (.i64 (UInt64.ofNat L)) :=
    Locals.get_setLocal_same hLow5 hHigh5
  have hI5 : s5.get base = some (.i64 (i.denote funs env)) :=
    (hF5.below base (by omega)).1.trans hI4
  have hP5 : s5.get (base + 1) = some (.i64 p) := (hF5.below _ (by omega)).1.trans hP4
  have hh5 : s5.positions = h := hF5.positions.trans hh4
  have hp5 : s5.params = s.params := hF5.params.trans hp4
  -- The test of the position.
  simp only [wpX_localGet_cons, Locals.get_values, hI5, hL5]
  rw [wpX_divCode hk, words_div hk hnk]
  simp only [wpX_ltUI64_cons]
  refine wpX_iff_cons rfl ?_
  have hLess : i.denote funs env < UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat < (env.get x).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hn64]
  by_cases hc : (i.denote funs env).toNat < (env.get x).size
  · rw [ite_eq_left (by simp [hLess.mpr hc])]
    set I := (i.denote funs env).toNat with hIdef
    set W := I * e.width with hWdef
    have hk29 : e.width < 536870912 := by
      have := Nat.le_mul_of_pos_left e.width (show 0 < (env.get x).size by omega); omega
    have hIk : W + e.width ≤ L := by
      have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hc)
      rw [Nat.succ_mul] at this; omega
    have hwc := wordCount_eq hk29
    -- The element's first word, in local `base + 3`.
    simp only [wpX_localGet_cons, Locals.get_values, hI5]
    have hs := words_scale hk (show I * e.width < 536870912 by omega)
    rw [UInt64.ofNat_toNat] at hs
    rw [wpX_scaleCode, hs]
    have hLow6 : ({ s5 with values := s5.values } : Locals).params.length ≤ base + 3 := by
      show s5.params.length ≤ _; rw [hp5]; omega
    have hHigh6' : base + 3 < s5.positions := by rw [hh5]; omega
    have hHigh6 := Locals.lt_total (s := { s5 with values := s5.values }) hHigh6'
    refine wpX_localSet_local hLow6 hHigh6 ?_
    set s6 : Locals := setLocal { s5 with values := s5.values } (base + 3) (.i64 (UInt64.ofNat W))
      with hs6
    have hF6 : Frame (base + 3) s5 s6 := Frame.setValues hLow6 le_rfl hHigh6'
    have hW6 : s6.get (base + 3) = some (.i64 (UInt64.ofNat W)) :=
      Locals.get_setLocal_same hLow6 hHigh6
    have hL6 : s6.get (base + 2) = some (.i64 (UInt64.ofNat L)) :=
      (hF6.below _ (by omega)).1.trans hL5
    have hP6 : s6.get (base + 1) = some (.i64 p) := (hF6.below _ (by omega)).1.trans hP5
    have hh6 : s6.positions = h := hF6.positions.trans hh5
    have hp6 : s6.params = s.params := hF6.params.trans hp5
    -- The count of words to move, in local `base + 4`.
    simp only [wpX_localGet_cons, Locals.get_values, hL6, hW6, wpX_subI64_cons, wpX_constI64_cons]
    have hCount : UInt64.ofNat L - UInt64.ofNat W - wordCount e.width =
        UInt64.ofNat (L - W - e.width) := by
      rw [hwc]
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_sub, UInt64.toNat_ofNat']
      omega
    rw [hCount]
    have hLow7 : ({ s6 with values := s6.values } : Locals).params.length ≤ base + 4 := by
      show s6.params.length ≤ _; rw [hp6]; omega
    have hHigh7' : base + 4 < s6.positions := by rw [hh6]; omega
    have hHigh7 := Locals.lt_total (s := { s6 with values := s6.values }) hHigh7'
    refine wpX_localSet_local hLow7 hHigh7 ?_
    set s7 : Locals := setLocal { s6 with values := s6.values } (base + 4)
      (.i64 (UInt64.ofNat (L - W - e.width))) with hs7
    have hF7 : Frame (base + 4) s6 s7 := Frame.setValues hLow7 le_rfl hHigh7'
    have hN7 : s7.get (base + 4) = some (.i64 (UInt64.ofNat (L - W - e.width))) :=
      Locals.get_setLocal_same hLow7 hHigh7
    have hW7 : s7.get (base + 3) = some (.i64 (UInt64.ofNat W)) :=
      (hF7.below _ (by omega)).1.trans hW6
    have hL7 : s7.get (base + 2) = some (.i64 (UInt64.ofNat L)) :=
      (hF7.below _ (by omega)).1.trans hL6
    have hP7 : s7.get (base + 1) = some (.i64 p) := (hF7.below _ (by omega)).1.trans hP6
    have hh7 : s7.positions = h := hF7.positions.trans hh6
    have hp7 : s7.params = s.params := hF7.params.trans hp6
    -- The source address, in local `base + 5`.
    simp only [wpX_localGet_cons, Locals.get_values, hP7, hW7, wpX_constI64_cons, wpX_addI64_cons,
      wpX_mulI64_cons]
    have hSrc : p + (UInt64.ofNat W + wordCount e.width) * 8 =
        p + UInt64.ofNat (8 * (W + e.width)) := by
      rw [hwc]; congr 1
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
      omega
    rw [hSrc]
    have hLow8 : ({ s7 with values := s7.values } : Locals).params.length ≤ base + 5 := by
      show s7.params.length ≤ _; rw [hp7]; omega
    have hHigh8' : base + 5 < s7.positions := by rw [hh7]; omega
    have hHigh8 := Locals.lt_total (s := { s7 with values := s7.values }) hHigh8'
    refine wpX_localSet_local hLow8 hHigh8 ?_
    set s8 : Locals := setLocal { s7 with values := s7.values } (base + 5)
      (.i64 (p + UInt64.ofNat (8 * (W + e.width)))) with hs8
    have hF8 : Frame (base + 5) s7 s8 := Frame.setValues hLow8 le_rfl hHigh8'
    have hS8 : s8.get (base + 5) = some (.i64 (p + UInt64.ofNat (8 * (W + e.width)))) :=
      Locals.get_setLocal_same hLow8 hHigh8
    have hN8 : s8.get (base + 4) = some (.i64 (UInt64.ofNat (L - W - e.width))) :=
      (hF8.below _ (by omega)).1.trans hN7
    have hW8 : s8.get (base + 3) = some (.i64 (UInt64.ofNat W)) :=
      (hF8.below _ (by omega)).1.trans hW7
    have hL8 : s8.get (base + 2) = some (.i64 (UInt64.ofNat L)) :=
      (hF8.below _ (by omega)).1.trans hL7
    have hP8 : s8.get (base + 1) = some (.i64 p) := (hF8.below _ (by omega)).1.trans hP7
    have hh8 : s8.positions = h := hF8.positions.trans hh7
    have hp8 : s8.params = s.params := hF8.params.trans hp7
    -- The destination address, in local `base + 6`.
    simp only [wpX_localGet_cons, Locals.get_values, hP8, hW8, wpX_constI64_cons, wpX_addI64_cons,
      wpX_mulI64_cons]
    have hDst : p + UInt64.ofNat W * 8 = p + UInt64.ofNat (8 * W) := by
      congr 1
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
      omega
    rw [hDst]
    have hLow9 : ({ s8 with values := s8.values } : Locals).params.length ≤ base + 6 := by
      show s8.params.length ≤ _; rw [hp8]; omega
    have hHigh9' : base + 6 < s8.positions := by rw [hh8]; omega
    have hHigh9 := Locals.lt_total (s := { s8 with values := s8.values }) hHigh9'
    refine wpX_localSet_local hLow9 hHigh9 ?_
    set s9 : Locals := setLocal { s8 with values := s8.values } (base + 6)
      (.i64 (p + UInt64.ofNat (8 * W))) with hs9
    have hF9 : Frame (base + 6) s8 s9 := Frame.setValues hLow9 le_rfl hHigh9'
    have hD9 : s9.get (base + 6) = some (.i64 (p + UInt64.ofNat (8 * W))) :=
      Locals.get_setLocal_same hLow9 hHigh9
    have hS9 : s9.get (base + 5) = some (.i64 (p + UInt64.ofNat (8 * (W + e.width)))) :=
      (hF9.below _ (by omega)).1.trans hS8
    have hN9 : s9.get (base + 4) = some (.i64 (UInt64.ofNat (L - W - e.width))) :=
      (hF9.below _ (by omega)).1.trans hN8
    have hL9 : s9.get (base + 2) = some (.i64 (UInt64.ofNat L)) :=
      (hF9.below _ (by omega)).1.trans hL8
    have hP9 : s9.get (base + 1) = some (.i64 p) := (hF9.below _ (by omega)).1.trans hP8
    have hh9 : s9.positions = h := hF9.positions.trans hh8
    have hp9 : s9.params = s.params := hF9.params.trans hp8
    -- The move of the words after the element.
    have hWs : (e.words (env.get x)).size = L := Elem.words_size e _
    refine wpX_copyDown (l := W) (n := L - W - e.width) (k := e.width) hA hPAl (by omega) hS9 hD9 hN9
      (by omega) (by omega) (by omega) (by rw [hp9]; omega)
      (Locals.lt_total (s := s9) (by rw [hh9]; omega))
      fun store10 s10 hW10 hA10 hp10 hl10 hOther10 hv10 => ?_
    have hP10 : s10.get (base + 1) = some (.i64 p) := by rw [hOther10 _ (by omega)]; exact hP9
    have hL10 : s10.get (base + 2) = some (.i64 (UInt64.ofNat L)) := by
      rw [hOther10 _ (by omega)]; exact hL9
    -- The shorter length.
    simp only [wpX_localGet_cons, Locals.get_values, hP10, hL10, wpX_wrapI64_cons, wrap_toUInt32,
      wpX_constI64_cons, wpX_subI64_cons]
    have hLen : UInt64.ofNat L - wordCount e.width = UInt64.ofNat (L - e.width) := by
      rw [hwc]
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_sub, UInt64.toNat_ofNat']
      omega
    rw [hLen]
    have hFit10 := hA10.1
    have hMem10 := hA10.2.1
    have hPtr := hA10.pointerAddress_toNat
    simp only [wpX_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by rw [hPtr]; rw [shiftDown_size] at hFit10 hMem10; omega)]
    refine ⟨fun hs => UInt64.toUInt32_mod8 (hPAl hs), ?_⟩
    rw [wpX_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, hP10]
    have hFrame : Frame (base + 1) s4 s10 :=
      (hF5.mono (by omega)).trans ((hF6.mono (by omega)).trans ((hF7.mono (by omega)).trans
        ((hF8.mono (by omega)).trans ((hF9.mono (by omega)).trans
          (Frame.ofOthers hp10 hl10 hOther10 (by omega) (by rw [hh9]; omega))))))
    have hEq : LeanExe.eraseAt (env.get x) (i.denote funs env) = (env.get x).eraseIdx I hc :=
      dite_eq_left hc
    rw [show s5.values = s10.values from hv10.symm]
    refine hFinish _ s10 _ hFrame hv10 (by rw [hEq]; exact Elem.words_eraseIdx e hc)
      ((a4.reframe hFrame).rewriteRange
        (hW10.trans (writeLength_frame store10 p (e.words (env.get x)).size (L - e.width)
          (by rw [shiftDown_size] at hFit10; exact hFit10)))
        (hA10.writeLength (by rw [shiftDown_size]; omega))
        (by simp only [Array.size_extract, shiftDown_size]; omega))
      (fun hs => ⟨(hAlO hs).1.1, Ty.AlignedVal.ownedArray (hPAl hs) (by
        rw [capacity_writesRange (by have := hOwned.base; omega) (by have := hOwned.address; omega)
          (hW10.trans (writeLength_frame store10 p (e.words (env.get x)).size (L - e.width)
            (by rw [shiftDown_size] at hFit10; exact hFit10)))]
        exact Ty.AlignedVal.arrayCap (hAlO hs).2)⟩)
  · rw [ite_eq_right (by simp [hLess, hc])]
    rw [wpX_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, wpX_localGet_cons, hP5]
    exact hFinish _ s5 (e.words (env.get x)) (hF5.mono (by omega)) rfl
      (by simp [LeanExe.eraseAt, Array.eraseIdxIfInBounds, hc]) (a4.reframe (hF5.mono (by omega)))
      (fun hs => ⟨(hAlO hs).1.1, Ty.AlignedVal.ownedArray (hPAl hs) (Ty.AlignedVal.arrayCap (hAlO hs).2)⟩)
/-- `LeanExe.insertAt x i v`: the position in local `base`, the value's words from local `base + 1`
on, their count after them, the array taken with room for one more element by `Var.roomCode` from
local `base + k + 2` on, and then, when the position is at most the size, the element's first word
in local `base + k + 4`, the move of the words from there up by the element's word count, and the
writes of the value's words, or otherwise the old length written back. -/
theorem specX_insertAt (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (hRt : strict = true → AllocAligned m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word} {v : Expr S Γ' (.elem e)}
    (iSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv i env slots paid live)
    (vSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv v env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.insertAt x i v) env
        slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi := Nat.le_max_left i.width (max (1 + v.width) (e.width + 8))
  have hv := (Nat.le_max_left (1 + v.width) (e.width + 8)).trans (Nat.le_max_right i.width _)
  have hx := (Nat.le_max_right (1 + v.width) (e.width + 8)).trans (Nat.le_max_right i.width _)
  have hk := e.width_pos
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  have hT : (Expr.insertAt x i v).allocs funs flags bounds (slots.map Slot.mode) paid live env =
      i.allocs funs flags bounds (slots.map Slot.mode) paid
          (fun j => live j || j == x.index || v.uses j) env +
        v.allocs funs flags bounds (slots.map Slot.mode) paid (fun j => live j || j == x.index) env +
        x.roomCost (slots.map Slot.mode) paid live (env.get x) (wordCount e.width).toNat := rfl
  have hdS : (Expr.insertAt x i v).fits funs fits env = true →
      i.fits funs fits env = true ∧ v.fits funs fits env = true :=
    fun hd => by simpa [Expr.fits] using hd
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc, List.cons_append, List.nil_append]
  -- The position, in local `base`.
  have hIn : ∀ k, ((live k || k == x.index || v.uses k) || i.uses k) = true →
      (live k || (Expr.insertAt x i v).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact set_live_index _ _ _ _ h
  -- The variables that die in the position, in the value, and the array when it dies.
  have hDiv : dyingPot store s env slots paid
        (fun k => (live k || k == x.index || v.uses k) || i.uses k)
        (fun k => live k || k == x.index || v.uses k) +
      dyingPot store s env slots paid (fun k => (live k || k == x.index) || v.uses k)
        (fun k => live k || k == x.index) +
      dyingPot store s env slots paid (fun k => live k || k == x.index) live ≤
      dyingPot store s env slots paid (fun k => live k || (Expr.insertAt x i v).uses k) live := by
    rw [dyingPot_split _ (fun k => live k || k == x.index || v.uses k) live
      (fun k h => hIn k (by simp [h])) (fun k h => by simp [h]),
      dyingPot_split (fun k => live k || k == x.index || v.uses k) (fun k => live k || k == x.index)
        live (fun k h => by simp [h]) (fun k h => by simp [h]),
      dyingPot_congr (L0 := fun k => live k || (Expr.insertAt x i v).uses k)
        (L0' := fun k => (live k || k == x.index || v.uses k) || i.uses k)
        (fun k => by simp only [Expr.uses, Bool.or_comm, Bool.or_left_comm])
        fun _ => rfl]
    omega
  refine iSpec env slots paid _ h base heap store s hh hpv
    (hVars.live_mono hIn) hAt (fun hs => (hAl hs).live_mono hIn) (hSafe.mono hIn) hCap hBase (by omega) hPlace.1 _ _
    (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun _ => by simp [Expr.aborts])
      fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hAlI hTopI => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  refine After.storeWordX a1 le_rfl hBase (by rw [hh]; omega) fun e1 hI1 => ?_
  have hp1 := e1.frame.params
  have hh1 := e1.frame.positions.trans hh
  -- The value's words, from local `base + 1` on.
  have hDv : ∀ s1' : Locals, Evolves env slots (fun k => (live k || k == x.index || v.uses k) ||
        i.uses k) (fun k => live k || k == x.index || v.uses k) base heap store s heap1 store1
        s1' →
      dyingPot store1 s1' env slots paid (fun k => (live k || k == x.index) || v.uses k)
        (fun k => live k || k == x.index) =
      dyingPot store s env slots paid (fun k => (live k || k == x.index) || v.uses k)
        (fun k => live k || k == x.index) := fun _ e =>
    dyingPot_evolves (hVars.live_mono hIn) e (fun k h => by simp [h]) _ _ fun _ h => h
  have hAlV0 := fun (hs : strict = true) => HoldsA.evolves (hVars.live_mono hIn)
    ((hAl hs).live_mono hIn) e1 (fun k h => by simp [h]) (hAlI hs).1.1
  refine vSpec env slots paid _ h (base + 1) heap1 store1 _ hh1
    (hp1.trans hpv) (e1.holds.mono (Nat.le_succ base)) e1.step.at_ hAlV0
    ((hSafe.mono hIn).evolves (hVars.live_mono hIn) e1 (fun k hk => by simp [hk])) (by rw [e1.step.cap m]; exact
        hCap)
    (by rw [hp1]; omega) (by omega) hPlace.2 _ _
    (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun _ => by simp [Expr.aborts])
      fun hd hw => by
        have := hTopI (hdS (fits_of_not hd)).1
        rw [hDv _ e1]
        exact hw.shift (c1 := dyingPot store s env slots paid
            (fun k => (live k || k == x.index || v.uses k) || i.uses k)
            (fun k => live k || k == x.index || v.uses k) +
            i.allocs funs flags bounds (slots.map Slot.mode) paid
              (fun j => live j || j == x.index || v.uses j) env)
          (by omega) (by rw [hT]; omega) (e1.step.cap m))
    fun heap2 store2 s2 ws2 a2 hAlV hTopV => ?_
  have hR2 := Ty.rep_elem.mp a2.rep
  subst hR2
  have e2a := a2.toEvolves rfl
  have hp2a : s2.params = s.params := e2a.frame.params.trans hp1
  have hh2a : s2.positions = h := e2a.frame.positions.trans hh1
  refine wpX_storeCode (e.values (v.denote funs env)) h (base + 1) e.types s2 s.values
    (by rw [e.values_length, e.types_length]) hh2a (by rw [hp2a]; omega)
    (by rw [e.types_length, hh2a]; omega) fun s2' f2 hold2 _ => ?_
  have f2' : Frame (base + 1) s2 { s2' with values := s.values } := f2.trans Frame.ofValues
  have e2 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) (base + 1) heap1 store1 _ heap2 store2
      { s2' with values := s.values } :=
    ⟨e2a.step, e2a.frame.trans f2', e2a.holds.agree f2'⟩
  have hp2 : s2'.params = s.params := f2.params.trans hp2a
  have hh2 : s2'.positions = h := f2.positions.trans hh2a
  have hI2 : s2'.get base = some (.i64 (i.denote funs env)) :=
    (e2.frame.below base (by omega)).1.trans hI1
  -- The count of new words, in local `base + k + 1`.
  simp only [wpX_constI64_cons]
  have hLowK : ({ s2' with values := s.values } : Locals).params.length ≤ base + e.width + 1 := by
    show s2'.params.length ≤ _; rw [hp2]; omega
  have hHighK' : base + e.width + 1 < ({ s2' with values := s.values } : Locals).positions := by
    simp only [Locals.positions_values, hh2]; omega
  have hHighK := Locals.lt_total hHighK'
  refine wpX_localSet_local hLowK hHighK ?_
  set s3 := setLocal { s2' with values := s.values } (base + e.width + 1)
    (.i64 (wordCount e.width)) with hs3
  have hK3 : s3.get (base + e.width + 1) = some (.i64 (wordCount e.width)) :=
    Locals.get_setLocal_same hLowK hHighK
  have hF3 : Frame (base + e.width + 1) { s2' with values := s.values } s3 :=
    Frame.setValues (s := { s2' with values := s.values }) (vs := s.values) hLowK le_rfl hHighK'
  have hold3 : LocalsHold s3 (base + 1) e.types (e.values (v.denote funs env)) :=
    (LocalsHold.frame (Frame.ofValues.trans hF3) (by rw [e.values_length, e.types_length])
      (by rw [e.types_length]; omega)).mpr hold2
  have e3 : Evolves env slots (fun k => (live k || k == x.index) || v.uses k)
      (fun k => live k || k == x.index) (base + 1) heap1 store1 _ heap2 store2 s3 :=
    ⟨e2.step, e2.frame.trans (hF3.mono (by omega)), e2.holds.agree (hF3.mono (by omega))⟩
  have hp3 : s3.params = s.params := e3.frame.params.trans hp1
  have hh3 : s3.positions = h := e3.frame.positions.trans hh1
  have hI3 : s3.get base = some (.i64 (i.denote funs env)) :=
    (hF3.below base (by omega)).1.trans hI2
  have hDx : dyingPot store2 s3 env slots paid (fun k => live k || k == x.index) live =
      dyingPot store s env slots paid (fun k => live k || k == x.index) live := by
    rw [dyingPot_evolves (e1.holds.mono (Nat.le_succ base)) e3 (fun k h => by simp [h]) _ _
      fun _ h => h]
    exact dyingPot_evolves (hVars.live_mono hIn) e1 (fun k h => by simp [h]) _ _
      fun k h => by simp [h]
  -- The array, with room for one more element, from local `base + k + 2` on.
  refine specX_room hm hRA hRt x (paid := paid) (b := base + e.width + 2) (ext := base + e.width + 1)
    (e := wordCount e.width) (s := s3) (e3.holds.mono (by omega))
    e3.step.at_
    (fun hs => HoldsA.evolves (e1.holds.mono (Nat.le_succ base)) (hAlV0 hs) e3
      (fun k h => by simp [h]) (hAlV hs).1.1) (by rw [e3.step.cap m, e1.step.cap m]; exact hCap) (by rw [hp3]; omega)
    (by rw [hh3]; omega) hK3 (by omega) (by rw [wordCount_toNat]; omega)
    (hTrap.alloc (by simp [Expr.aborts]) fun hd hw => hw.of_le
      (by
        have := hTopI (hdS (fits_of_not hd)).1; have h2 := hTopV (hdS (fits_of_not hd)).2
        rw [hDv _ e1] at h2
        rw [hDx]; rw [hT] at hw; omega)
      (by rw [e3.step.cap m, e1.step.cap m]))
    fun heap3 store3 s4 q words hSize hPrefix aR hN4 hQ4 hv4 hAlR hTopR => ?_
  obtain ⟨p0, hp0, hOwnedQ⟩ := aR.rep
  replace hOwnedQ : heap3.Owned store3 p0 words := hOwnedQ
  obtain rfl : p0 = q := by simp only [List.cons.injEq, Value.i64.injEq] at hp0; exact hp0.1.symm
  have hQAl : strict = true → p0.toNat % 8 = 0 := fun hs =>
    Ty.AlignedVal.ownedPtr (by have := hOwnedQ.base; omega) (hAlR hs).2
  have hAQ := hOwnedQ.values
  have hFitQ := hAQ.1
  have hMemQ := hAQ.2.1
  have hPtrQ := hAQ.pointerAddress_toNat
  have hWs : (e.words (env.get x)).size = (env.get x).size * e.width := Elem.words_size e _
  have hk29 : e.width < 536870912 := by
    rw [wordCount_toNat] at hSize; omega
  have hkw : (wordCount e.width).toNat = e.width := by rw [wordCount_toNat]; omega
  rw [hkw, hWs] at hSize
  have hnk : (env.get x).size * e.width < 536870912 := by omega
  have hn64 : (env.get x).size < UInt64.size := by
    have := Nat.le_mul_of_pos_right (env.get x).size hk
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega
  have hN4' : s4.get (base + e.width + 3) =
      some (.i64 (UInt64.ofNat ((env.get x).size * e.width))) := by
    rw [← hWs]; exact hN4
  have hQ4' : s4.get (base + e.width + 6) = some (.i64 p0) := hQ4
  have hPrefix' : ∀ w, w < (env.get x).size * e.width →
      words[w]! = (e.words (env.get x))[w]! := fun w hw => by
    rw [hPrefix w (by rw [hWs]; exact hw), getElem!_pos _ w (by rw [hWs]; exact hw)]
  have hp4 : s4.params = s.params := aR.frame.params.trans hp3
  have hh4 : s4.positions = h := aR.frame.positions.trans hh3
  have hI4 : s4.get base = some (.i64 (i.denote funs env)) :=
    (aR.frame.below base (by omega)).1.trans hI3
  have hold4 : LocalsHold s4 (base + 1) e.types (e.values (v.denote funs env)) :=
    (LocalsHold.frame aR.frame (by rw [e.values_length, e.types_length])
      (by rw [e.types_length]; omega)).mpr hold3
  -- The rest of the code, from the array after the writes or with the old length.
  have hCapW : ∀ (store' : Store Unit) (ws' : Array UInt64),
      Memory.WritesRange store3 store' p0.toNat (p0.toNat + 8 * (words.size + 1)) →
      UInt64Array.At store' p0 ws' → ws'.size ≤ words.size →
      capacityAt store' p0 = capacityAt store3 p0 := fun store' ws' hW hA hLe => by
    have := hOwnedQ.capacity
    exact (hOwnedQ.rewrite ⟨by rw [hW.1], hW.2.1, fun a ha => hW.2.2 a (by omega)⟩ hA
      (by omega)).2
  rw [hDx] at hTopR
  have hFinish : ∀ (store5 : Store Unit) (s' : Locals) (ws : Array UInt64),
      s'.values = s.values →
      ws = e.words (LeanExe.insertAt (env.get x) (i.denote funs env) (v.denote funs env)) →
      capacityAt store5 p0 = capacityAt store3 p0 → ws.size ≤ words.size →
      After env slots (fun k => live k || k == x.index) live (base + e.width + 2) heap2 store2 s3
        (.array .word) .owned ws heap3 store5 s' [.i64 p0] →
      wpX strict m rest Q store5 { s' with values := .i64 p0 :: s'.values } host := by
    rintro store5 s' ws hv' rfl hCap5 hLe aX
    have aX1 := (After.ofWords aX).lower e3.holds (by omega) fun k h => by simp [h]
    have aX2 := After.prepend (e1.holds.mono (Nat.le_succ base)) e3 aX1
      (fun k h => by simp [h]) fun k h => by simp [h]
    have aX3 := After.prepend (hVars.live_mono hIn) e1 (aX2.lower e1.holds (Nat.le_succ base)
      fun k h => by simp [h]) (fun k h => by simp [h]) fun k h => by simp [h]
    have hBound : (Expr.insertAt x i v).fits funs fits env = true →
        heap3.top.toNat + (if (Expr.insertAt x i v).paid flags (slots.map Slot.mode) paid live then
            (Ty.array e).pot store5 [.i64 p0] ((Expr.insertAt x i v).denote funs env) else 0) ≤
          heap.top.toNat + dyingPot store s env slots paid
            (fun k => live k || (Expr.insertAt x i v).uses k) live +
            (Expr.insertAt x i v).allocs funs flags bounds (slots.map Slot.mode) paid live env := by
      intro hd
      have := hTopI (hdS hd).1; have h2 := hTopV (hdS hd).2
      rw [hDv _ e1] at h2
      have hPot : (Ty.array e).pot store5 [.i64 p0] ((Expr.insertAt x i v).denote funs env) ≤
          arrayPot store3 p0 words.size := by
        show arrayPot store5 p0 (e.words (LeanExe.insertAt (env.get x) (i.denote funs env)
          (v.denote funs env))).size ≤ _
        unfold arrayPot; rw [hCap5]; omega
      rw [hT]
      show heap3.top.toNat + (if (modeAt (slots.map Slot.mode) x.index == .owned &&
          !live x.index) = true then _ else 0) ≤ _
      by_cases hc : (slots.getD x.index default).mode = .owned ∧ live x.index = false
      · rw [ite_eq_left hc] at hTopR
        rw [ite_eq_left
            (by simp only [modeAt, Slot.modes_getD, hc.1, hc.2, beq_self_eq_true, Bool.not_false,
        Bool.and_self])]
        omega
      · rw [ite_eq_right hc] at hTopR
        rw [ite_eq_right (by
          simp only [modeAt, Slot.modes_getD, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
          exact hc)]
        omega
    simpa [hv'] using hNext heap3 store5 _ [.i64 p0] (aX3.liveIn hIn)
      (fun hs => ⟨HoldsA.after hVars (hAl hs) (aX3.liveIn hIn) (fun k h => by simp [h]) (hAlR hs).1,
        Ty.AlignedVal.ownedArray (hQAl hs) (by rw [hCap5]; exact Ty.AlignedVal.arrayCap (hAlR hs).2)⟩)
      hBound
  -- The test of the position.
  simp only [wpX_localGet_cons, Locals.get_values, hI4, hN4']
  rw [wpX_divCode hk, words_div hk hnk]
  simp only [wpX_leUI64_cons]
  refine wpX_iff_cons rfl ?_
  have hLe : i.denote funs env ≤ UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat ≤ (env.get x).size := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hn64]
  by_cases hc : (i.denote funs env).toNat ≤ (env.get x).size
  · rw [ite_eq_left (by simp [hLe.mpr hc])]
    have hWL : (i.denote funs env).toNat * e.width ≤ (env.get x).size * e.width :=
      Nat.mul_le_mul_right _ hc
    -- The element's first word, in local `base + k + 4`.
    simp only [wpX_localGet_cons, Locals.get_values, hI4]
    have hs := words_scale hk (show (i.denote funs env).toNat * e.width < 536870912 by omega)
    rw [UInt64.ofNat_toNat] at hs
    rw [wpX_scaleCode, hs]
    have hLow5 : ({ s4 with values := s4.values } : Locals).params.length ≤ base + e.width + 4 := by
      show s4.params.length ≤ _; rw [hp4]; omega
    have hHigh5' : base + e.width + 4 < s4.positions := by rw [hh4]; omega
    have hHigh5 := Locals.lt_total (s := { s4 with values := s4.values }) hHigh5'
    refine wpX_localSet_local hLow5 hHigh5 ?_
    set s5 : Locals := setLocal { s4 with values := s4.values } (base + e.width + 4)
      (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) with hs5
    have hF5 : Frame (base + e.width + 4) s4 s5 := Frame.setValues hLow5 le_rfl hHigh5'
    have hW5 : s5.get (base + e.width + 4) =
        some (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) :=
      Locals.get_setLocal_same hLow5 hHigh5
    have hN5 : s5.get (base + e.width + 3) =
        some (.i64 (UInt64.ofNat ((env.get x).size * e.width))) :=
      (hF5.below _ (by omega)).1.trans hN4'
    have hQ5 : s5.get (base + e.width + 6) = some (.i64 p0) := by
      rw [Locals.get_setLocal_ne hLow5 (by omega)]; exact hQ4'
    have hh5 : s5.positions = h := hF5.positions.trans hh4
    have hp5 : s5.params = s.params := hF5.params.trans hp4
    -- The old length, in local `base + k + 7`.
    simp only [wpX_localGet_cons, hN5]
    have hLow6 : ({ s5 with values := s5.values } : Locals).params.length ≤ base + e.width + 7 := by
      show s5.params.length ≤ _; rw [hp5]; omega
    have hHigh6' : base + e.width + 7 < s5.positions := by rw [hh5]; omega
    have hHigh6 := Locals.lt_total (s := { s5 with values := s5.values }) hHigh6'
    refine wpX_localSet_local hLow6 hHigh6 ?_
    set s6 : Locals := setLocal { s5 with values := s5.values } (base + e.width + 7)
      (.i64 (UInt64.ofNat ((env.get x).size * e.width))) with hs6
    have hF6 : Frame (base + e.width + 7) s5 s6 := Frame.setValues hLow6 le_rfl hHigh6'
    have hL6 : s6.get (base + e.width + 7) =
        some (.i64 (UInt64.ofNat ((env.get x).size * e.width))) :=
      Locals.get_setLocal_same hLow6 hHigh6
    have hW6 : s6.get (base + e.width + 4) =
        some (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) :=
      (hF6.below _ (by omega)).1.trans hW5
    have hQ6 : s6.get (base + e.width + 6) = some (.i64 p0) :=
      (hF6.below _ (by omega)).1.trans hQ5
    have hh6 : s6.positions = h := hF6.positions.trans hh5
    have hp6 : s6.params = s.params := hF6.params.trans hp5
    -- The move of the words from the element's first word up.
    refine wpX_shiftUp (ptr := base + e.width + 6) (lo := base + e.width + 4)
      (index := base + e.width + 7) (k := e.width) (l := (i.denote funs env).toNat * e.width)
      (h := (env.get x).size * e.width) hAQ hQAl hWL (by omega) hQ6 hW6 hL6 (by omega) (by omega)
      (by rw [hp6]; omega) (Locals.lt_total (s := s6) (by rw [hh6]; omega))
      fun store7 s7 hW7 hA7 hp7 hl7 hOther7 hv7 => ?_
    have hQ7 : s7.get (base + e.width + 6) = some (.i64 p0) := by
      rw [hOther7 _ (by omega)]; exact hQ6
    have hW7' : s7.get (base + e.width + 4) =
        some (.i64 (UInt64.ofNat ((i.denote funs env).toNat * e.width))) := by
      rw [hOther7 _ (by omega)]; exact hW6
    have hFrame7 : Frame (base + e.width + 2) s4 s7 :=
      (hF5.mono (by omega)).trans ((hF6.mono (by omega)).trans
        (Frame.ofOthers hp7 hl7 hOther7 (by omega) (by rw [hh6]; omega)))
    have aS := (aR.reframe hFrame7).rewriteRange hW7 hA7 (by rw [shiftUp_size])
    have hold7 : LocalsHold s7 (base + 1) e.types
        (List.zipWith typedValue e.types (e.toWords (v.denote funs env))) := by
      rw [e.values_typed]
      exact (LocalsHold.frame hFrame7 (by rw [e.values_length, e.types_length])
        (by rw [e.types_length]; omega)).mpr hold4
    have hW64 : (UInt64.ofNat ((i.denote funs env).toNat * e.width)).toNat =
        (i.denote funs env).toNat * e.width :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    -- The writes of the value's words.
    rw [← List.append_nil (storeWordsCode h (base + e.width + 6) (base + e.width + 4) 0 (base + 1)
      e.types)]
    refine wpX_storeWordsCode hQAl 0 (base + 1) e.types (e.toWords (v.denote funs env))
      (shiftUp words ((i.denote funs env).toNat * e.width) ((env.get x).size * e.width) e.width)
      store7 s7 aS (hFrame7.positions.trans hh4) hQ7 hW7' hold7
      (by rw [e.toWords_length, e.types_length]) (e.typed_words _)
      (by rw [hW64, e.types_length, shiftUp_size, hSize]; omega) fun store8 a8 hCap8 => ?_
    rw [hW64] at a8
    simp only [Nat.add_zero] at a8
    have hEq : LeanExe.insertAt (env.get x) (i.denote funs env) (v.denote funs env) =
        (env.get x).insertIdx (i.denote funs env).toNat (v.denote funs env) hc := dite_eq_left hc
    rw [wpX_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, hQ7]
    rw [show s4.values = s7.values from (hv7.trans rfl).symm]
    exact hFinish store8 s7 _ (hv7.trans hv4)
      (by rw [hEq]; exact Elem.words_insertIdx e (v.denote funs env) hc hSize hPrefix')
      (hCap8.trans (hCapW store7 _ hW7 hA7 (le_of_eq (shiftUp_size ..))))
      (le_of_eq (by rw [writeWords_size, shiftUp_size])) a8
  · rw [ite_eq_right (by simp [hLe, hc])]
    simp only [wpX_localGet_cons, Locals.get_values, hQ4', wpX_wrapI64_cons, wrap_toUInt32, hN4']
    simp only [wpX_store64_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
    rw [ite_eq_right (by rw [hPtrQ]; omega)]
    refine ⟨fun hs => UInt64.toUInt32_mod8 (hQAl hs), ?_⟩
    rw [wpX_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, hQ4']
    have hEq : LeanExe.insertAt (env.get x) (i.denote funs env) (v.denote funs env) = env.get x :=
      dite_eq_right hc
    have hWL := writeLength_frame store3 p0 words.size ((env.get x).size * e.width) hFitQ
    have hAL := hAQ.writeLength (by omega : (env.get x).size * e.width ≤ words.size)
    exact hFinish _ s4 _ hv4
      (by rw [hEq]; exact Elem.words_extract_prefix e (by omega) hPrefix')
      (hCapW _ _ hWL hAL (by simp only [Array.size_extract]; omega))
      (by simp only [Array.size_extract]; omega)
      (aR.rewriteRange hWL hAL (by simp only [Array.size_extract]; omega))

/-- `LeanExe.insertAt x i v`: the position in local `base`, the value's words from local `base + 1`
on, their count after them, the array taken with room for one more element by `Var.roomCode` from
local `base + k + 2` on, and then, when the position is at most the size, the element's first word
in local `base + k + 4`, the move of the words from there up by the element's word count, and the
writes of the value's words, or otherwise the old length written back. -/
theorem spec_insertAt (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word} {v : Expr S Γ' (.elem e)}
    (iSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv i env slots paid live)
    (vSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv v env slots paid live) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.insertAt x i v) env
        slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_insertAt (strict := false) hm nofun nofun x
      (fun env slots paid live => CodeSpecX.false_iff.mpr (iSpec env slots paid live))
      (fun env slots paid live => CodeSpecX.false_iff.mpr (vSpec env slots paid live)) env slots
      paid live)

end Cases

end Verified
