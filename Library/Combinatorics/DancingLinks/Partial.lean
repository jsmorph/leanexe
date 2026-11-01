import Library.Combinatorics.DancingLinks.Build

/-! The array while step X1 reads the options.  `Partial t L Mc j` states the array after the
options before `Mc` and the first `j` nodes of option `Mc`: its size, the list of all items, the
columns of the nodes made so far, the spacers up to `Mc` with their links, and zeros in every word
of the nodes not yet made.  `partial_append` adds the next node, `partial_close` adds the spacer
after a finished option, and `partial_final` turns `Partial t L M 0` into the invariant of the
search for all items. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

/-- The nodes below `p`. -/
def made (L : Layout) (p : Nat) : Finset Nat :=
  (range (L.first L.os.length)).filter fun q => L.IsNode q ∧ q < p

/-- The array after the options before `Mc` and the first `j` nodes of option `Mc`. -/
structure Partial (t : Array UInt64) (L : Layout) (Mc j : Nat) : Prop where
  size : t.size = L.base + 2 * (L.n + 1)
  items : Items t L (Icc 1 L.n)
  cols : Cols t L (Icc 1 L.n) (made L (L.first Mc + j))
  spacer : ∀ k ≤ Mc, W t (3 * (L.first k - 1)) = 0
  up : ∀ k < Mc, W t (3 * (L.first (k + 1) - 1) + 1) = L.first k
  down : ∀ k < Mc, W t (3 * (L.first k - 1) + 2) = L.first k + L.len k - 1
  future : ∀ q, L.first Mc + j ≤ q → q < L.first L.os.length → ∀ r < 3, t[3 * q + r]! = 0

theorem colQ_made_insert {L : Layout} {p c : Nat} (hp : L.IsNode p) (hpc : L.nodeItem p = c)
    (hpM : p < L.first L.os.length) :
    L.colQ (made L (p + 1)) c = insert p (L.colQ (made L p) c) := by
  ext q
  simp only [Layout.colQ, made, mem_filter, mem_insert, mem_range]
  constructor
  · rintro ⟨⟨hq, hqn, hqp⟩, hqc⟩
    rcases Nat.lt_or_ge q p with h | h
    · exact Or.inr ⟨⟨hq, hqn, h⟩, hqc⟩
    · exact Or.inl (by omega)
  · rintro (rfl | ⟨⟨hq, hqn, hqp⟩, hqc⟩)
    · exact ⟨⟨hpM, hp, by omega⟩, hpc⟩
    · exact ⟨⟨hq, hqn, by omega⟩, hqc⟩

theorem colQ_made_other {L : Layout} {p c : Nat} (hpc : L.nodeItem p ≠ c) :
    L.colQ (made L (p + 1)) c = L.colQ (made L p) c := by
  ext q
  simp only [Layout.colQ, made, mem_filter, mem_range]
  constructor
  · rintro ⟨⟨hq, hqn, hqp⟩, hqc⟩
    refine ⟨⟨hq, hqn, ?_⟩, hqc⟩
    rcases Nat.lt_or_ge q p with h | h
    · exact h
    · exact absurd (show q = p by omega ▸ hqc) hpc
  · rintro ⟨⟨hq, hqn, hqp⟩, hqc⟩
    exact ⟨⟨hq, hqn, by omega⟩, hqc⟩

/-- Adding the next node of option `Mc`. -/
theorem partial_append {t : Array UInt64} {L : Layout} (hL : L.Good) {Mc j : Nat}
    (h : Partial t L Mc j) (hMc : Mc < L.os.length) (hj : j < L.len Mc) :
    Partial (append t (L.item Mc j) (L.first Mc + j)) L Mc (j + 1) := by
  set p := L.first Mc + j with hp
  set c := L.item Mc j with hc
  have hat : L.At p Mc j := ⟨hMc, hj, rfl⟩
  have hpn : L.IsNode p := L.at_isNode hat
  have hpc : L.nodeItem p = c := Layout.nodeItem_at hat
  have hcI : c ∈ Icc 1 L.n := mem_Icc.mpr (hL.items Mc hMc j hj)
  have hpM := (L.node_lt hpn).2
  have hsmall := hL.small
  have hcol := h.cols.col c hcI
  have hps : 3 * p + 2 < t.size := by rw [h.size, Layout.base]; omega
  have hts : t.size < 2 ^ 62 := by rw [h.size]; omega
  have hbelow : ∀ y ∈ insert c (L.colQ (made L p) c), y < p := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · have := L.n_lt_first Mc; have := (hL.items Mc hMc j hj).2; omega
    · have := mem_filter.mp (colQ_node hy).1; exact this.2.2
  set u := prv c (L.colQ (made L p) c) c with hu_def
  have hu : u ∈ insert c (L.colQ (made L p) c) := prv_mem_insert c _ c
  have hframe : ∀ k, (∀ y, (y = c ∨ y = p ∨ y = u) → ∀ r < 3, k ≠ 3 * y + r) →
      (append t c p)[k]! = t[k]! := append_frame hcol hps
  have hcn := (hL.items Mc hMc j hj).2
  -- The written nodes: the header, the new node, and the column's last node.
  have hw : ∀ y, (y = c ∨ y = p ∨ y = u) →
      (y = c ∨ (L.IsNode y ∧ (y = p ∨ L.nodeItem y = c))) ∧ y ≤ p := by
    rintro y (rfl | rfl | rfl)
    · exact ⟨Or.inl rfl, Nat.le_of_lt (hbelow _ (mem_insert_self _ _))⟩
    · exact ⟨Or.inr ⟨hpn, Or.inl rfl⟩, le_rfl⟩
    · refine ⟨?_, Nat.le_of_lt (hbelow _ hu)⟩
      rcases mem_insert.mp hu with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨(mem_filter.mp (colQ_node h').1).2.1, Or.inr (colQ_node h').2⟩
  have hnode_gt : ∀ y, L.IsNode y → L.n + 1 < y := fun y hy => (L.node_lt hy).1
  -- A word index `3y + r` is written only when `y` is a written node.
  have hidx : ∀ k y, (∀ y', (y' = c ∨ y' = p ∨ y' = u) → y ≠ y') → ∀ r < 3, k = 3 * y + r →
      (append t c p)[k]! = t[k]! := by
    intro k y hne r hr hk
    refine hframe k fun y' hy' r' hr' he => hne y' hy' (by omega)
  -- A spacer is no written node.
  have hsp : ∀ k ≤ L.os.length, ∀ y', (y' = c ∨ y' = p ∨ y' = u) → L.first k - 1 ≠ y' := by
    intro k hk y' hy' he
    have := L.n_lt_first k
    rcases (hw y' hy').1 with h' | ⟨hn, _⟩
    · omega
    · exact L.spacer_not_node hk (he ▸ hn)
  refine ⟨by rw [append_size]; exact h.size, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rw [W, hframe _ fun y' hy' r hr => ?_]
      · exact h.items.left y hy
      · have := node_words_lt (L := L) (y := y') (by
          rcases (hw y' hy').1 with h' | ⟨hn, _⟩
          · exact Or.inl (by rw [h']; exact hcn)
          · exact Or.inr hn) r hr
        omega
    · rw [W, hframe _ fun y' hy' r hr => ?_]
      · exact h.items.right y hy
      · have := node_words_lt (L := L) (y := y') (by
          rcases (hw y' hy').1 with h' | ⟨hn, _⟩
          · exact Or.inl (by rw [h']; exact hcn)
          · exact Or.inr hn) r hr
        omega
  · refine ⟨fun q hq => (mem_filter.mp hq).2.1, h.cols.items, fun c' hc' => ?_⟩
    rw [show L.first Mc + (j + 1) = p + 1 by omega]
    by_cases hcc : c' = c
    · rw [hcc, colQ_made_insert hpn hpc hpM]
      exact col_append hcol hbelow hps hts
    · rw [colQ_made_other (fun e => hcc (by rw [← e, hpc]))]
      have hc'n := (mem_Icc.mp hc').2
      refine (h.cols.col c' hc').frame (append_size t c p) fun y hy r hr =>
        hidx _ y (fun y' hy' he => ?_) r hr rfl
      subst he
      rcases mem_insert.mp hy with rfl | hy
      · rcases (hw y hy').1 with h' | ⟨hn, _⟩
        · exact hcc h'
        · have := hnode_gt y hn; omega
      · obtain ⟨hyP, hyc⟩ := colQ_node hy
        have hyp := (mem_filter.mp hyP).2.2
        rcases (hw y hy').1 with h' | ⟨hn, h''⟩
        · have := hnode_gt y (mem_filter.mp hyP).2.1; omega
        · rcases h'' with h'' | h''
          · omega
          · exact hcc (hyc.symm.trans h'')
  · intro k hk
    rw [W, hidx _ _ (hsp k (by have := hMc; omega)) 0 (by omega) (by omega)]
    exact h.spacer k hk
  · intro k hk
    rw [W, hidx _ _ (hsp (k + 1) (by omega)) 1 (by omega) rfl]
    exact h.up k hk
  · intro k hk
    rw [W, hidx _ _ (hsp k (by omega)) 2 (by omega) rfl]
    exact h.down k hk
  · intro q hq hqM r hr
    rw [hframe _ fun y' hy' r' hr' he => by have := (hw y' hy').2; omega]
    exact h.future q (by omega) hqM r hr

/-- The writes that finish option `Mc`: the spacer after it points back to the option's first node,
and the spacer before it points forward to the option's last node. -/
def close (L : Layout) (t : Array UInt64) (Mc : Nat) : Array UInt64 :=
  (t.set! (3 * (L.first (Mc + 1) - 1) + 1) (UInt64.ofNat (L.first Mc))).set!
    (3 * (L.first Mc - 1) + 2) (UInt64.ofNat (L.first (Mc + 1) - 2))

theorem made_spacer {L : Layout} {k : Nat} (hk : k ≤ L.os.length) :
    made L (L.first k) = made L (L.first k - 1) := by
  have hn := L.n_lt_first k
  ext q
  simp only [made, mem_filter]
  constructor
  · rintro ⟨hq, hqn, hqk⟩
    refine ⟨hq, hqn, ?_⟩
    rcases Nat.lt_or_ge q (L.first k - 1) with h | h
    · exact h
    · exact absurd (show q = L.first k - 1 by omega ▸ hqn) (L.spacer_not_node hk)
  · rintro ⟨hq, hqn, hqk⟩
    exact ⟨hq, hqn, by omega⟩

/-- Finishing option `Mc` after its last node. -/
theorem partial_close {t : Array UInt64} {L : Layout} (hL : L.Good) {Mc : Nat}
    (h : Partial t L Mc (L.len Mc)) (hMc : Mc < L.os.length) :
    Partial (close L t Mc) L (Mc + 1) 0 := by
  have hsmall := hL.small
  have hlen := hL.nonempty Mc hMc
  have hlast := L.first_le_last hMc
  have hsucc := L.first_succ Mc
  have hn := L.n_lt_first Mc
  set p := L.first (Mc + 1) - 1 with hp
  set sp := L.first Mc - 1 with hsp
  have hpM : p < L.first L.os.length := by omega
  have hsz : t.size = L.base + 2 * (L.n + 1) := h.size
  have hb : 3 * L.first L.os.length ≤ L.base := le_of_eq rfl
  have hget : ∀ k, (close L t Mc)[k]! =
      if k = 3 * sp + 2 then UInt64.ofNat (L.first (Mc + 1) - 2)
      else if k = 3 * p + 1 then UInt64.ofNat (L.first Mc) else t[k]! := by
    intro k
    unfold close
    rw [get_set _ _ _ _ (by simp only [Array.size_set!]; omega), get_set _ _ _ _ (by omega)]
  have hspn : ∀ k ≤ L.os.length, ¬ L.IsNode (L.first k - 1) := fun k hk => L.spacer_not_node hk
  have hfar : ∀ k, (k ≠ 3 * sp + 2 ∧ k ≠ 3 * p + 1) → (close L t Mc)[k]! = t[k]! := by
    intro k hk
    rw [hget, ite_eq_right hk.1, ite_eq_right hk.2]
  have hcolw : ∀ y, (y ≤ L.n ∨ L.IsNode y) → y ≠ sp ∧ y ≠ p := by
    intro y hy
    rcases hy with hy | hy
    · omega
    · refine ⟨fun e => hspn Mc (Nat.le_of_lt hMc) ?_, fun e => hspn (Mc + 1) (by omega) ?_⟩
      · rw [← hsp, ← e]; exact hy
      · rw [← hp, ← e]; exact hy
  have hc64 : L.first Mc < 2 ^ 64 := by unfold Layout.base at hsmall; omega
  have hp64 : L.first (Mc + 1) - 2 < 2 ^ 64 := by unfold Layout.base at hsmall; omega
  refine ⟨by unfold close; simp [hsz], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun y hy => ?_, fun y hy => ?_⟩ <;>
    · have hy' : y ≤ L.n := by
        rcases mem_insert.mp hy with rfl | hy
        · omega
        · exact (mem_Icc.mp hy).2
      rw [W, hfar _ ⟨by unfold Layout.base; omega, by unfold Layout.base; omega⟩]
      first | exact h.items.left y hy | exact h.items.right y hy
  · rw [Nat.add_zero, made_spacer (Nat.succ_le_of_lt hMc), ← hp,
      show p = L.first Mc + L.len Mc by omega]
    refine ⟨h.cols.nodes, h.cols.items, fun c hc => ?_⟩
    refine (h.cols.col c hc).frame (by unfold close; simp) fun y hy r hr => hfar _ ?_
    have hy' : y ≤ L.n ∨ L.IsNode y := by
      rcases mem_insert.mp hy with rfl | hy
      · exact Or.inl (mem_Icc.mp hc).2
      · exact Or.inr (h.cols.nodes y (colQ_node hy).1)
    obtain ⟨h1, h2⟩ := hcolw y hy'
    constructor <;> omega
  · intro k hk
    rcases Nat.lt_or_ge k (Mc + 1) with hk' | hk'
    · rw [W, hfar _ ⟨fun he => by
          have := L.first_le (show k ≤ Mc by omega); have := L.n_lt_first k; omega,
        fun he => by omega⟩]
      exact h.spacer k (by omega)
    · have hkM : k = Mc + 1 := by omega
      subst hkM
      rw [W, hfar _ ⟨by omega, by omega⟩, ← hp,
        show 3 * p = 3 * p + 0 by rfl, h.future p (by omega) hpM 0 (by omega)]
      rfl
  · intro k hk
    rcases Nat.lt_or_ge k Mc with hk' | hk'
    · have := L.first_le (show k + 1 ≤ Mc by omega)
      rw [W, hfar _ ⟨by omega, fun he => by
          have : L.first (k + 1) - 1 = p := by omega
          have := L.first_lt (show k + 1 < Mc + 1 by omega)
          omega⟩]
      exact h.up k hk'
    · have hkM : k = Mc := by omega
      subst hkM
      rw [W, ← hp, hget, ite_eq_right (by omega), ite_eq_left rfl,
        UInt64.toNat_ofNat_of_lt' hc64]
  · intro k hk
    rcases Nat.lt_or_ge k Mc with hk' | hk'
    · have := L.first_lt hk'
      rw [W, hfar _ ⟨fun he => by omega, by omega⟩]
      exact h.down k hk'
    · have hkM : k = Mc := by omega
      subst hkM
      rw [W, ← hsp, hget, ite_eq_left rfl, UInt64.toNat_ofNat_of_lt' hp64]
      omega
  · intro q hq hqM r hr
    rw [hfar _ ⟨by omega, by omega⟩]
    exact h.future q (by omega) hqM r hr

/-- After the last option, the array holds the invariant of the search for all items. -/
theorem partial_final {t : Array UInt64} {L : Layout} (hL : L.Good)
    (h : Partial t L L.os.length 0) : Inv t L (Icc 1 L.n) := by
  have hpres : made L (L.first L.os.length + 0) = L.present (Icc 1 L.n) := by
    ext q
    simp only [made, Layout.present, mem_filter, Nat.add_zero]
    constructor
    · rintro ⟨hq, hqn, _⟩
      refine ⟨hq, hqn, fun j hj => ?_⟩
      have hat := Layout.at_of_isNode hqn
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hj
      have := hL.items _ hat.1 m hm
      unfold Layout.item at this
      rw [getElem!_pos _ m hm] at this
      exact mem_Icc.mpr this
    · rintro ⟨hq, hqn, _⟩
      exact ⟨hq, hqn, mem_range.mp hq⟩
  have hcols := h.cols
  rw [hpres] at hcols
  refine ⟨⟨h.size, fun k hk m hm => ?_, h.spacer, h.up, h.down⟩,
    fun c hc => mem_Icc.mp hc, h.items, hcols⟩
  have hat : L.At (L.first k + m) k m := ⟨hk, hm, rfl⟩
  have hI : L.item k m ∈ Icc 1 L.n := mem_Icc.mpr (hL.items k hk m hm)
  have hcol := hcols.col _ hI
  have hq : L.first k + m ∈ L.colQ (L.present (Icc 1 L.n)) (L.item k m) := by
    refine mem_filter.mpr ⟨(L.mem_present hat).mpr fun j hj => ?_, Layout.nodeItem_at hat⟩
    obtain ⟨m', hm', rfl⟩ := List.getElem_of_mem hj
    have := hL.items k hk m' hm'
    unfold Layout.item at this
    rw [getElem!_pos _ m' hm'] at this
    exact mem_Icc.mpr this
  exact hcol.top _ hq

end Library.Combinatorics.DancingLinks
