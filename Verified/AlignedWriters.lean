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

end Verified
