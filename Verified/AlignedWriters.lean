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

/-- An owned array whose pointer and capacity are multiples of 8 is aligned. -/
theorem Ty.AlignedVal.ownedArray {store : Store Unit} {e : Elem} {p : UInt64}
    {xs : Array e.denote} (hp : p.toNat % 8 = 0) (hc : capacityAt store p % 8 = 0) :
    Ty.AlignedVal .owned store (.array e) [.i64 p] xs := by
  intro r hr
  simp only [Ty.regions, Ty.blocks, List.mem_singleton] at hr
  subst hr
  simp only [block]
  exact ⟨by omega, fun _ => by omega⟩

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

end Cases

end Verified
