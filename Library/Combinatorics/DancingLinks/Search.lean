import Library.Combinatorics.DancingLinks.Others

/-! The recursive search.  `search_eq` states that on an array with `Inv` of the active items `B`
and a depth bound `d` of at least `|B|`, `search d b` returns the number of exact covers of `B` by
the options inside `B`, modulo `2^64`, and the same array.  The proof is an induction on `d`.  With
no active item, the empty set of options is the one cover.  Otherwise the search covers the chosen
item `i`, and its loop visits the present nodes of the column of `i` in increasing order, which
`cover_inv` keeps.  For each node, `coverOthers` leaves the invariant of `B` without the option's
items, the induction gives that count, and `uncoverOthers` and `next` restore the array and step
to the next node.  The column's nodes correspond one to one to the options inside `B` that hold
`i`, so `column_sum` gives the sum as `coversOf_rec` at `i`. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

theorem Layout.Good.nonempty' {L : Layout} (hL : L.Good) : Nonempty' L.os := fun k hk => by
  have := hL.nonempty k hk
  unfold Layout.len at this
  intro he
  rw [he] at this
  simp at this

/-- The count of a column's node: the covers of `B` without the items of the node's option. -/
def nodeCount' (L : Layout) (B : Finset Nat) (r : Nat) : Nat :=
  coversOf L.os (B \ (L.os[L.optOf r]!).toFinset)

/-- The sum over the present nodes of the column of `i` is the count of covers of `B`. -/
theorem column_sum {L : Layout} (hL : L.Good) {B : Finset Nat} {i : Nat} (hi : i ∈ B) :
    ((colList (L.colQ (L.present B) i)).map (nodeCount' L B)).sum = coversOf L.os B := by
  rw [coversOf_rec L.os hL.nonempty' hi, ← List.sum_toFinset _ (colList_nodup _)]
  have hset : (colList (L.colQ (L.present B) i)).toFinset = L.colQ (L.present B) i := by
    ext y; simp [mem_colList]
  rw [hset]
  refine Finset.sum_nbij' (fun r => L.optOf r) (fun k => L.first k +
      (L.os[k]!).idxOf i) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    obtain ⟨hrP, hri⟩ := colQ_node (mem_coe.mp hr)
    obtain ⟨_, hrn, hin⟩ := mem_filter.mp hrP
    have hat := Layout.at_of_isNode hrn
    refine mem_coe.mpr (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hat.1, hin⟩, ?_⟩)
    rw [← hri, Layout.nodeItem_at hat]
    unfold Layout.item
    have hl : r - L.first (L.optOf r) < (L.os[L.optOf r]!).length := hat.2.1
    rw [getElem!_pos (L.os[L.optOf r]!) _ hl]
    exact List.getElem_mem _
  · intro k hk
    obtain ⟨hkin, hik⟩ := mem_filter.mp (mem_coe.mp hk)
    obtain ⟨hkr, hkB⟩ := mem_filter.mp hkin
    have hidx : (L.os[k]!).idxOf i < (L.os[k]!).length := List.idxOf_lt_length_of_mem hik
    have hat : L.At (L.first k + (L.os[k]!).idxOf i) k ((L.os[k]!).idxOf i) :=
      ⟨mem_range.mp hkr, hidx, rfl⟩
    refine mem_coe.mpr (mem_filter.mpr ⟨(L.mem_present hat).mpr hkB, ?_⟩)
    rw [Layout.nodeItem_at hat]
    unfold Layout.item
    rw [getElem!_pos (L.os[k]!) _ hidx]
    exact List.getElem_idxOf hidx
  · intro r hr
    obtain ⟨hrP, hri⟩ := colQ_node (mem_coe.mp hr)
    obtain ⟨_, hrn, _⟩ := mem_filter.mp hrP
    have hat := Layout.at_of_isNode hrn
    have hl : r - L.first (L.optOf r) < (L.os[L.optOf r]!).length := hat.2.1
    have hitem : (L.os[L.optOf r]!)[r - L.first (L.optOf r)] = i := by
      rw [← hri, Layout.nodeItem_at hat]; unfold Layout.item
      rw [getElem!_pos (L.os[L.optOf r]!) _ hl]
    have hnd := hL.nodup _ hat.1
    have : (L.os[L.optOf r]!).idxOf i = r - L.first (L.optOf r) := by
      rw [← hitem]; exact List.Nodup.idxOf_getElem hnd _ hl
    rw [this]
    have := hat.2.2
    omega
  · intro k hk
    obtain ⟨hkin, hik⟩ := mem_filter.mp (mem_coe.mp hk)
    obtain ⟨hkr, _⟩ := mem_filter.mp hkin
    have hidx : (L.os[k]!).idxOf i < (L.os[k]!).length := List.idxOf_lt_length_of_mem hik
    exact Layout.optOf_at ⟨mem_range.mp hkr, hidx, rfl⟩
  · intro r hr
    rfl

theorem idx_b1 (b : UInt64) (h : b.toNat + 1 < 2 ^ 64) : (b + 1).toNat = b.toNat + 1 := by
  simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega

/-- The search counts the exact covers of the active items and restores the array. -/
theorem search_eq {L : Layout} (hL : L.Good) {b : UInt64} (hb : b.toNat = L.base) :
    ∀ (n : Nat) (d : UInt64) (t : Array UInt64) (B : Finset Nat), d.toNat = n → Inv t L B →
      B.card ≤ n → search d b t = (UInt64.ofNat (coversOf L.os B), t) := by
  intro n
  induction n with
  | zero =>
    intro d t B hd h hB
    have hB0 : B = ∅ := card_eq_zero.mp (by omega)
    subst hB0
    have hrl : t[(b + 1).toNat]! = 0 := by
      have hsmall := hL.small
      rw [idx_b1 b (by omega), hb]
      have := h.items.right 0 (mem_insert_self 0 ∅)
      unfold nxt at this
      rw [dite_eq_right (by simp)] at this
      exact UInt64.toNat_inj.mp (by rw [← W, this]; rfl)
    rw [search, dite_eq_left (Or.inl hrl), ite_eq_left hrl, coversOf_empty _ hL.nonempty']
    rfl
  | succ n ih =>
    intro d t B hd h hB
    have hsmall := hL.small
    have hsize : t.size = L.base + 2 * (L.n + 1) := h.static.size
    have hA : Above 0 B := fun c hc => (h.sub c hc).1
    by_cases hB0 : B = ∅
    · subst hB0
      have hrl : t[(b + 1).toNat]! = 0 := by
        rw [idx_b1 b (by omega), hb]
        have := h.items.right 0 (mem_insert_self 0 ∅)
        unfold nxt at this
        rw [dite_eq_right (by simp)] at this
        exact UInt64.toNat_inj.mp (by rw [← W, this]; rfl)
      rw [search, dite_eq_left (Or.inl hrl), ite_eq_left hrl, coversOf_empty _ hL.nonempty']
      rfl
    have hne : B.Nonempty := nonempty_iff_ne_empty.mpr hB0
    have hrl : t[(b + 1).toNat]! ≠ 0 := by
      rw [idx_b1 b (by omega), hb]
      intro h0
      have e := h.items.right 0 (mem_insert_self 0 B)
      simp only [Nat.mul_zero, Nat.add_zero] at e
      rw [W, h0, UInt64.toNat_zero] at e
      unfold nxt at e
      have hne' : (B.filter (0 < ·)).Nonempty := by
        obtain ⟨y, hy⟩ := hne
        exact ⟨y, mem_filter.mpr ⟨hy, hA y hy⟩⟩
      rw [dite_eq_left hne'] at e
      have hpos := (mem_filter.mp (min'_mem _ hne')).2
      omega
    have hd0 : d ≠ 0 := by
      intro h0; rw [h0] at hd; simp at hd
    rw [search, dite_eq_right (by rintro (h' | h') <;> contradiction)]
    dsimp only
    -- The chosen item and its column.
    set i := choose b t with hi_def
    have hiB : i.toNat ∈ B := choose_mem hL hb h hne
    obtain ⟨h1, hunc, hcol1⟩ := cover_inv hL h hb hiB
    set Q := L.colQ (L.present B) i.toNat with hQ
    set t1 := coverItem b i t with ht1
    have hcolt : Col t i.toNat Q := h.cols.col _ hiB
    have hAQ : Above i.toNat Q := hcolt.above
    have hnd := colList_nodup Q
    have hidx : ∀ j' (hj' : j' < (colList Q).length), (colList Q).idxOf (colList Q)[j'] = j' :=
      fun j' hj' => List.Nodup.idxOf_getElem hnd j' hj'
    have hcard : (colList Q).length < t.size := by
      rw [colList_length]
      have hsub : insert i.toNat Q ⊆ range t.size := by
        intro z hz
        have := hcolt.size z hz
        exact mem_range.mpr (by omega)
      have := card_le_card hsub
      rw [card_insert_of_notMem (fun hm => Nat.lt_irrefl _ (hAQ _ hm)), card_range] at this
      omega
    have hiS := hcolt.size _ (mem_insert_self _ _)
    -- The facts about one node of the column.
    have hnode : ∀ r : UInt64, r.toNat ∈ Q →
        L.At r.toNat (L.optOf r.toNat) (r.toNat - L.first (L.optOf r.toNat)) ∧
          L.item (L.optOf r.toNat) (r.toNat - L.first (L.optOf r.toNat)) = i.toNat ∧
          (∀ j ∈ (L.os[L.optOf r.toNat]!).toFinset.erase i.toNat, j ∈ B.erase i.toNat) ∧
          B.erase i.toNat \ ((L.os[L.optOf r.toNat]!).toFinset.erase i.toNat) =
            B \ (L.os[L.optOf r.toNat]!).toFinset ∧
          (B \ (L.os[L.optOf r.toNat]!).toFinset).card ≤ n := by
      intro r hr
      obtain ⟨hrP, hri⟩ := colQ_node hr
      obtain ⟨_, hrn, hin⟩ := mem_filter.mp hrP
      have hat := Layout.at_of_isNode hrn
      have hitem : L.item (L.optOf r.toNat) (r.toNat - L.first (L.optOf r.toNat)) = i.toNat := by
        rw [← hri, Layout.nodeItem_at hat]
      have himem : i.toNat ∈ (L.os[L.optOf r.toNat]!).toFinset := by
        rw [List.mem_toFinset, ← hitem]
        unfold Layout.item
        have hl : r.toNat - L.first (L.optOf r.toNat) < (L.os[L.optOf r.toNat]!).length := hat.2.1
        rw [getElem!_pos (L.os[L.optOf r.toNat]!) _ hl]
        exact List.getElem_mem _
      refine ⟨hat, hitem, ?_, ?_, ?_⟩
      · intro j hj
        obtain ⟨hji, hj'⟩ := mem_erase.mp hj
        exact mem_erase.mpr ⟨hji, hin j (List.mem_toFinset.mp hj')⟩
      · ext y
        simp only [mem_sdiff, mem_erase]
        constructor
        · rintro ⟨⟨hyi, hyB⟩, hy⟩
          exact ⟨hyB, fun hy' => hy ⟨hyi, hy'⟩⟩
        · rintro ⟨hyB, hy⟩
          refine ⟨⟨fun e => hy (e ▸ himem), hyB⟩, fun h' => hy h'.2⟩
      · have : B \ (L.os[L.optOf r.toNat]!).toFinset ⊂ B := by
          refine ⟨sdiff_subset, fun hs => ?_⟩
          have := hs hiB
          exact (mem_sdiff.mp this).2 himem
        have := card_lt_card this
        omega
    let Inv' : UInt64 × UInt64 × Array UInt64 → Prop := fun s => s.2.2 = t1 ∧
      ∃ j ≤ (colList Q).length,
        s.1.toNat = (if h : j < (colList Q).length then (colList Q)[j] else i.toNat) ∧
          s.2.1 = UInt64.ofNat (((colList Q).take j).map (nodeCount' L B)).sum
    let μ : UInt64 × UInt64 × Array UInt64 → Nat := fun s =>
      if s.1.toNat = i.toNat then 0 else (colList Q).length - (colList Q).idxOf s.1.toNat
    have hμle : ∀ s, μ s ≤ (colList Q).length := fun s => by
      show (if _ then _ else _) ≤ _
      split
      · exact Nat.zero_le _
      · exact Nat.sub_le _ _
    have hfuel : μ (t[(3 * i + 2).toNat]!, 0, t1) < t.size.toUInt64.toNat := by
      have := hμle (t[(3 * i + 2).toNat]!, 0, t1)
      rw [size_toUInt64 t (by omega)]
      omega
    have hinit : Inv' (t[(3 * i + 2).toNat]!, 0, t1) := by
      refine ⟨rfl, 0, Nat.zero_le _, ?_, by simp⟩
      show (t[(3 * i + 2).toNat]!).toNat = _
      obtain ⟨-, -, e2⟩ := idx3 i (by omega)
      rw [e2, ← W, hcolt.down _ (mem_insert_self _ _), nxt_head_colList hAQ]
    have hloop := repeatWhile_of_inv t.size.toUInt64 (t[(3 * i + 2).toNat]!, (0 : UInt64), t1)
      (fun s => decide (s.1 ≠ i))
      (fun s => next b s.1 s.2.1 (search (d - 1) b (coverOthers b s.1 s.2.2)).1
        (search (d - 1) b (coverOthers b s.1 s.2.2)).2) Inv' μ
      (fun s => s.2.2 = t1 ∧ s.2.1 = UInt64.ofNat (coversOf L.os B)) hinit hfuel ?_ ?_
    · obtain ⟨hs2, hs1⟩ := hloop
      rw [hs1, hs2, hunc]
    · rintro ⟨r, acc, t'⟩ ⟨ht, j, hj, hr, hacc⟩ hcond
      simp only [ne_eq, decide_eq_true_eq] at hcond
      dsimp only at ht hr hacc ⊢
      have hlt : j < (colList Q).length := by
        by_contra hne'
        rw [dite_eq_right hne'] at hr
        exact hcond (UInt64.toNat_inj.mp hr)
      rw [dite_eq_left hlt] at hr
      have hrQ : r.toNat ∈ Q := by rw [hr]; exact mem_colList.mp (List.getElem_mem hlt)
      obtain ⟨hat, _, hin, hset, hcardr⟩ := hnode r hrQ
      obtain ⟨heq, hinv2⟩ := coverOthers_eq hL hb h1 hat (by rw [(hnode r hrQ).2.1]; exact hin)
      rw [(hnode r hrQ).2.1, hset] at hinv2
      have hd1 : (d - 1).toNat = n := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
      have hrec := ih (d - 1) (coverOthers b r t1) _ hd1 hinv2 hcardr
      have hunc2 := uncoverOthers_eq hL hb h1 hat (by rw [(hnode r hrQ).2.1]; exact hin)
      obtain ⟨-, -, e2⟩ := idx3 r (by
        have := hcol1.size _ (mem_insert_of_mem hrQ); have := h1.static.size; omega)
      have hnext : (t1[(3 * r + 2).toNat]!).toNat =
          (if h : j + 1 < (colList Q).length then (colList Q)[j + 1] else i.toNat) := by
        rw [e2, ← W, hcol1.down _ (mem_insert_of_mem hrQ), hr, nxt_colList j hlt]
      have hstep : (next b r acc (search (d - 1) b (coverOthers b r t')).1
          (search (d - 1) b (coverOthers b r t')).2) =
          (t1[(3 * r + 2).toNat]!, acc + UInt64.ofNat (nodeCount' L B r.toNat), t1) := by
        rw [ht, hrec]
        unfold next
        dsimp only
        rw [hunc2]
        rfl
      refine ⟨?_, ?_⟩
      · show Inv' (next b r acc (search (d - 1) b (coverOthers b r t')).1
          (search (d - 1) b (coverOthers b r t')).2)
        rw [hstep]
        refine ⟨rfl, j + 1, by omega, hnext, ?_⟩
        rw [hacc, List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ← hr,
          UInt64.ofNat_add]
      · show μ (next b r acc (search (d - 1) b (coverOthers b r t')).1
          (search (d - 1) b (coverOthers b r t')).2) < μ (r, acc, t')
        rw [hstep]
        show (if _ then _ else _) < (if _ then _ else _)
        rw [hnext, hr]
        have hne0 : (colList Q)[j] ≠ i.toNat :=
          Nat.ne_of_gt (hAQ _ (mem_colList.mp (List.getElem_mem hlt)))
        rw [ite_eq_right hne0, hidx j hlt]
        by_cases h1' : j + 1 < (colList Q).length
        · have hne1 : (colList Q)[j + 1] ≠ i.toNat :=
            Nat.ne_of_gt (hAQ _ (mem_colList.mp (List.getElem_mem h1')))
          rw [dite_eq_left h1', ite_eq_right hne1, hidx (j + 1) h1']
          omega
        · rw [dite_eq_right h1', ite_eq_left rfl]
          omega
    · rintro ⟨r, acc, t'⟩ ⟨ht, j, hj, hr, hacc⟩ hc
      simp only [decide_eq_false_iff_not, not_not] at hc
      dsimp only at ht hr hacc hc ⊢
      have hjl : j = (colList Q).length := by
        by_contra hne'
        have hlt : j < (colList Q).length := by omega
        rw [dite_eq_left hlt, hc] at hr
        have := hAQ _ (mem_colList.mp (List.getElem_mem hlt))
        omega
      refine ⟨ht, ?_⟩
      rw [hacc, hjl, List.take_length, column_sum hL hiB]

end Library.Combinatorics.DancingLinks
