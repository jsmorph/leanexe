import Library.Combinatorics.DancingLinks.Walk
import Mathlib.Data.Finset.Sort

/-! The loops of Knuth's `cover(i)` and `uncover(i)` over a column.  `colList Q` lists the present
nodes of a column in increasing order, and `nxt` and `prv` step along it.  `hideColumn i` hides the
options of the column's nodes from the top down, so `hideColumn_eq` writes it as `delAll` of the
concatenation `colOthers` of their `others`, and `unhideColumn_eq` shows that the walk from the
bottom up, which unhides them in the reverse order, returns the array.  The nodes of the
concatenation lie in other columns, since no option holds an item twice, so the column itself
keeps its links, which both walks read. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

/-- The present nodes of a column, in increasing order. -/
def colList (Q : Finset Nat) : List Nat := Q.sort (· ≤ ·)

theorem colList_sorted (Q : Finset Nat) : (colList Q).Pairwise (· < ·) :=
  Q.sortedLT_sort.pairwise

theorem mem_colList {Q : Finset Nat} {y : Nat} : y ∈ colList Q ↔ y ∈ Q := Q.mem_sort _

theorem colList_nodup (Q : Finset Nat) : (colList Q).Nodup := Q.sort_nodup _

theorem colList_length (Q : Finset Nat) : (colList Q).length = Q.card := Q.length_sort _

theorem sorted_lt {l : List Nat} (hl : l.Pairwise (· < ·)) {a b : Nat} (ha : a < l.length)
    (hb : b < l.length) (hab : a < b) : l[a] < l[b] :=
  List.pairwise_iff_getElem.mp hl a b ha hb hab

theorem sorted_le_iff {l : List Nat} (hl : l.Pairwise (· < ·)) {a b : Nat} (ha : a < l.length)
    (hb : b < l.length) : l[a] < l[b] ↔ a < b := by
  constructor
  · intro h
    by_contra hn
    rcases Nat.lt_or_ge b a with hlt | hge
    · have := sorted_lt hl hb ha hlt; omega
    · have : a = b := by omega
      subst this; omega
  · exact sorted_lt hl ha hb

/-- The successor of node `j` of the list is node `j + 1`, or the header after the last. -/
theorem nxt_colList {c : Nat} {Q : Finset Nat} (j : Nat) (hj : j < (colList Q).length) :
    nxt c Q (colList Q)[j] = if h : j + 1 < (colList Q).length then (colList Q)[j + 1] else c := by
  have hs := colList_sorted Q
  unfold nxt
  split
  · rename_i hne
    split
    · rename_i h
      apply le_antisymm
      · exact min'_le _ _ (mem_filter.mpr ⟨mem_colList.mp (List.getElem_mem h),
          sorted_lt hs hj h (by omega)⟩)
      · apply le_min'
        intro y hy
        obtain ⟨hyQ, hyl⟩ := mem_filter.mp hy
        obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem (mem_colList.mpr hyQ)
        have := (sorted_le_iff hs hj hb).mp hyl
        rcases Nat.lt_or_ge (j + 1) b with h' | h'
        · exact Nat.le_of_lt (sorted_lt hs h hb h')
        · have : b = j + 1 := by omega
          subst this; exact le_rfl
    · rename_i h
      exfalso
      obtain ⟨y, hy⟩ := hne
      obtain ⟨hyQ, hyl⟩ := mem_filter.mp hy
      obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem (mem_colList.mpr hyQ)
      have := (sorted_le_iff hs hj hb).mp hyl
      omega
  · rename_i hne
    split
    · rename_i h
      exact absurd ⟨_, mem_filter.mpr ⟨mem_colList.mp (List.getElem_mem h),
        sorted_lt hs hj h (by omega)⟩⟩ hne
    · rfl

/-- The successor of the header is the first node, or the header for an empty column. -/
theorem nxt_head_colList {c : Nat} {Q : Finset Nat} (hA : Above c Q) :
    nxt c Q c = if h : 0 < (colList Q).length then (colList Q)[0] else c := by
  have hs := colList_sorted Q
  unfold nxt
  split
  · rename_i hne
    split
    · rename_i h
      apply le_antisymm
      · exact min'_le _ _ (mem_filter.mpr ⟨mem_colList.mp (List.getElem_mem h),
          hA _ (mem_colList.mp (List.getElem_mem h))⟩)
      · apply le_min'
        intro y hy
        obtain ⟨hyQ, _⟩ := mem_filter.mp hy
        obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem (mem_colList.mpr hyQ)
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · subst h0; exact le_rfl
        · exact Nat.le_of_lt (sorted_lt hs h hb h0)
    · rename_i h
      exfalso
      obtain ⟨y, hy⟩ := hne
      have := List.length_pos_of_mem (mem_colList.mpr (mem_filter.mp hy).1)
      omega
  · rename_i hne
    split
    · rename_i h
      exact absurd ⟨_, mem_filter.mpr ⟨mem_colList.mp (List.getElem_mem h),
        hA _ (mem_colList.mp (List.getElem_mem h))⟩⟩ hne
    · rfl

/-- The predecessor of node `j + 1` of the list is node `j`, and that of the first node is the
header. -/
theorem prv_colList {c : Nat} {Q : Finset Nat} (hA : Above c Q) (j : Nat)
    (hj : j < (colList Q).length) :
    prv c Q (colList Q)[j] = if h : 0 < j then (colList Q)[j - 1] else c := by
  have hs := colList_sorted Q
  have hmem := mem_colList.mp (List.getElem_mem hj)
  have hjc : (colList Q)[j] ≠ c := Nat.ne_of_gt (hA _ hmem)
  unfold prv
  rw [ite_eq_right hjc]
  split
  · rename_i hne
    split
    · rename_i h
      apply le_antisymm
      · apply max'_le
        intro y hy
        obtain ⟨hyQ, hyl⟩ := mem_filter.mp hy
        obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem (mem_colList.mpr hyQ)
        have := (sorted_le_iff hs hb hj).mp hyl
        rcases Nat.lt_or_ge b (j - 1) with h' | h'
        · exact Nat.le_of_lt (sorted_lt hs hb (by omega) h')
        · have : b = j - 1 := by omega
          subst this; exact le_rfl
      · exact le_max' _ _ (mem_filter.mpr ⟨mem_colList.mp (List.getElem_mem
          (show j - 1 < (colList Q).length by omega)),
          sorted_lt hs (a := j - 1) (b := j) (by omega) hj (by omega)⟩)
    · rename_i h
      exfalso
      obtain ⟨y, hy⟩ := hne
      obtain ⟨hyQ, hyl⟩ := mem_filter.mp hy
      obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem (mem_colList.mpr hyQ)
      have := (sorted_le_iff hs hb hj).mp hyl
      omega
  · rename_i hne
    split
    · rename_i h
      exact absurd ⟨_, mem_filter.mpr ⟨mem_colList.mp (List.getElem_mem
        (show j - 1 < (colList Q).length by omega)),
        sorted_lt hs (a := j - 1) (b := j) (by omega) hj (by omega)⟩⟩ hne
    · rfl

/-- The predecessor of the header is the last node, or the header for an empty column. -/
theorem prv_head_colList (c : Nat) (Q : Finset Nat) :
    prv c Q c = if h : 0 < (colList Q).length then (colList Q)[(colList Q).length - 1] else c := by
  have hs := colList_sorted Q
  unfold prv
  rw [ite_eq_left rfl]
  split
  · rename_i hne
    split
    · rename_i h
      apply le_antisymm
      · apply max'_le
        intro y hy
        obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem (mem_colList.mpr hy)
        rcases Nat.lt_or_ge b ((colList Q).length - 1) with h' | h'
        · exact Nat.le_of_lt (sorted_lt hs hb (by omega) h')
        · have : b = (colList Q).length - 1 := by omega
          subst this; exact le_rfl
      · exact le_max' _ _ (mem_colList.mp (List.getElem_mem (by omega)))
    · rename_i h
      exfalso
      obtain ⟨y, hy⟩ := hne
      have := List.length_pos_of_mem (mem_colList.mpr hy)
      omega
  · rename_i hne
    split
    · rename_i h
      exact absurd ⟨_, mem_colList.mp (List.getElem_mem h)⟩ hne
    · rfl

namespace Layout

/-- The nodes that `hide` removes for node `r`. -/
def oth (L : Layout) (r : Nat) : List Nat := L.others (L.optOf r) (r - L.first (L.optOf r))

theorem mem_others {L : Layout} {k m q : Nat} (hm : m < L.len k) :
    q ∈ L.others k m ↔ ∃ m', m' < L.len k ∧ m' ≠ m ∧ q = L.first k + m' := by
  unfold others
  simp only [List.mem_append, List.mem_range'_1]
  constructor
  · rintro (h | h)
    · exact ⟨q - L.first k, by omega, by omega, by omega⟩
    · exact ⟨q - L.first k, by omega, by omega, by omega⟩
  · rintro ⟨m', hm', hne, rfl⟩
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · right; omega
    · left; omega

theorem at_of_isNode {L : Layout} {r : Nat} (h : L.IsNode r) :
    L.At r (L.optOf r) (r - L.first (L.optOf r)) := (L.isNode_iff r).mp h

/-- Two nodes of one option that hold the same item are one node. -/
theorem node_eq_of_item {L : Layout} (hL : L.Good) {r r' k m m' : Nat} (h : L.At r k m)
    (h' : L.At r' k m') (hi : L.item k m = L.item k m') : r = r' := by
  have hnd := hL.nodup k h.1
  have hm : m < (L.os[k]!).length := h.2.1
  have hm' : m' < (L.os[k]!).length := h'.2.1
  unfold item at hi
  rw [getElem!_pos _ m hm, getElem!_pos _ m' hm'] at hi
  have := (List.Nodup.getElem_inj_iff hnd).mp hi
  rw [h.2.2, h'.2.2, this]

end Layout

/-- The nodes that `hideColumn` removes for the nodes `l` of a column, in its order. -/
def colOthers (L : Layout) (l : List Nat) : List Nat := l.flatMap L.oth

theorem colOthers_take_succ (L : Layout) (l : List Nat) (j : Nat) (hj : j < l.length) :
    colOthers L (l.take (j + 1)) = colOthers L (l.take j) ++ L.oth l[j] := by
  unfold colOthers
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append,
    List.flatMap_singleton]

/-- The facts about the present nodes of column `i` that the column's loops use: each node's
`others` lie in other present columns, and the `others` of distinct nodes are disjoint. -/
theorem colOthers_facts {L : Layout} (hL : L.Good) {B : Finset Nat} {i : Nat} (l : List Nat) (hl : l.Nodup) (hsub : ∀ r ∈ l, r ∈ L.colQ (L.present B) i) :
    (colOthers L l).Nodup ∧
      ∀ q ∈ colOthers L l, q ∈ L.present B ∧ L.nodeItem q ∈ B ∧ L.nodeItem q ≠ i := by
  have hnode : ∀ r ∈ l, L.IsNode r ∧ Inside L.os B (L.optOf r) ∧ L.nodeItem r = i := by
    intro r hr
    obtain ⟨hrP, hri⟩ := colQ_node (hsub r hr)
    have := mem_filter.mp hrP
    exact ⟨this.2.1, this.2.2, hri⟩
  have hq : ∀ r ∈ l, ∀ q ∈ L.oth r, q ∈ L.present B ∧ L.nodeItem q ∈ B ∧ L.nodeItem q ≠ i := by
    intro r hr q hq
    obtain ⟨hrn, hrin, hri⟩ := hnode r hr
    have hat := Layout.at_of_isNode hrn
    obtain ⟨m', hm', hne, rfl⟩ := (Layout.mem_others hat.2.1).mp hq
    have hat' : L.At (L.first (L.optOf r) + m') (L.optOf r) m' := ⟨hat.1, hm', rfl⟩
    refine ⟨(L.mem_present hat').mpr hrin, ?_, ?_⟩
    · rw [Layout.nodeItem_at hat']
      apply hrin
      unfold Layout.item
      have hm'l : m' < (L.os[L.optOf r]!).length := hm'
      rw [getElem!_pos _ m' hm'l]
      exact List.getElem_mem _
    · intro he
      rw [Layout.nodeItem_at hat'] at he
      rw [Layout.nodeItem_at hat] at hri
      have := Layout.node_eq_of_item hL hat' hat (he.trans hri.symm)
      omega
  refine ⟨?_, fun q hq' => ?_⟩
  · unfold colOthers
    refine List.nodup_flatMap.mpr ⟨fun r _ => Layout.others_nodup _ _ _, ?_⟩
    refine hl.pairwise_of_forall_ne fun r hr r' hr' hne => ?_
    intro q hq hq'
    obtain ⟨hrn, _, hri⟩ := hnode r hr
    obtain ⟨hrn', _, hri'⟩ := hnode r' hr'
    have hat := Layout.at_of_isNode hrn
    have hat' := Layout.at_of_isNode hrn'
    obtain ⟨m1, hm1, _, e1⟩ := (Layout.mem_others hat.2.1).mp hq
    obtain ⟨m2, hm2, _, e2⟩ := (Layout.mem_others hat'.2.1).mp hq'
    have hq1 : L.At q (L.optOf r) m1 := ⟨hat.1, hm1, e1⟩
    have hq2 : L.At q (L.optOf r') m2 := ⟨hat'.1, hm2, e2⟩
    obtain ⟨hk, -⟩ := Layout.at_unique hq1 hq2
    rw [Layout.nodeItem_at hat] at hri
    rw [Layout.nodeItem_at hat'] at hri'
    rw [← hk] at hat' hri'
    exact hne (Layout.node_eq_of_item hL hat hat' (hri.trans hri'.symm))
  · obtain ⟨r, hr, hqr⟩ := List.mem_flatMap.mp hq'
    exact hq r hr q hqr

/-- The present columns other than `i` after the options of column `i` are hidden. -/
theorem colQ_cover {L : Layout} {B : Finset Nat} {i c : Nat} (hc : c ≠ i) :
    L.colQ (L.present B \ (colOthers L (colList (L.colQ (L.present B) i))).toFinset) c =
      L.colQ (L.present (B.erase i)) c := by
  ext y
  simp only [Layout.colQ, mem_filter, mem_sdiff, List.mem_toFinset]
  constructor
  · rintro ⟨⟨hyP, hyH⟩, hyc⟩
    refine ⟨?_, hyc⟩
    obtain ⟨hyr, hyn, hyin⟩ := mem_filter.mp hyP
    refine mem_filter.mpr ⟨hyr, hyn, fun j hj => mem_erase.mpr ⟨?_, hyin j hj⟩⟩
    rintro rfl
    -- The option of `y` holds `i`, so its node in column `i` hides `y`.
    apply hyH
    have hat := Layout.at_of_isNode hyn
    have hjl : j ∈ L.os[L.optOf y]! := hj
    obtain ⟨m', hm', he⟩ := List.getElem_of_mem hjl
    have hat' : L.At (L.first (L.optOf y) + m') (L.optOf y) m' := ⟨hat.1, hm', rfl⟩
    have hitem : L.item (L.optOf y) m' = j := by
      unfold Layout.item; rw [getElem!_pos _ m' hm']; exact he
    have hrQ : L.first (L.optOf y) + m' ∈ L.colQ (L.present B) j :=
      mem_filter.mpr ⟨(L.mem_present hat').mpr hyin, by rw [Layout.nodeItem_at hat', hitem]⟩
    refine List.mem_flatMap.mpr ⟨_, mem_colList.mpr hrQ, ?_⟩
    unfold Layout.oth
    rw [Layout.optOf_at hat', show L.first (L.optOf y) + m' - L.first (L.optOf y) = m' by omega]
    have hy := hat.2.2
    refine (Layout.mem_others hm').mpr ⟨y - L.first (L.optOf y), hat.2.1, ?_, by omega⟩
    intro he'
    apply hc
    rw [← hyc, Layout.nodeItem_at hat, he', hitem]
  · rintro ⟨hyP, hyc⟩
    obtain ⟨hyr, hyn, hyin⟩ := mem_filter.mp hyP
    refine ⟨⟨mem_filter.mpr ⟨hyr, hyn, fun j hj => (mem_erase.mp (hyin j hj)).2⟩, ?_⟩, hyc⟩
    intro hyH
    obtain ⟨r, hr, hyr'⟩ := List.mem_flatMap.mp hyH
    obtain ⟨hrP, hri⟩ := colQ_node (mem_colList.mp hr)
    have hrn := (mem_filter.mp hrP).2.1
    have hat := Layout.at_of_isNode hrn
    obtain ⟨m', hm', _, e⟩ := (Layout.mem_others hat.2.1).mp hyr'
    have hyat : L.At y (L.optOf r) m' := ⟨hat.1, hm', e⟩
    rw [Layout.optOf_at hyat] at hyin
    have := hyin (L.item (L.optOf r) (r - L.first (L.optOf r))) (by
      unfold Layout.item
      have hl : r - L.first (L.optOf r) < (L.os[L.optOf r]!).length := hat.2.1
      rw [getElem!_pos (L.os[L.optOf r]!) _ hl]; exact List.getElem_mem _)
    rw [← Layout.nodeItem_at hat, hri] at this
    exact (mem_erase.mp this).1 rfl

theorem colOthers_prefix (L : Layout) (l : List Nat) (j : Nat) :
    colOthers L (l.take j) <+: colOthers L l := by
  unfold colOthers
  conv_rhs => rw [← List.take_append_drop j l]
  rw [List.flatMap_append]
  exact List.prefix_append _ _

/-- The removals of a prefix of a column's `colOthers` keep the static words, the columns, and the
column itself, whose nodes they do not change. -/
theorem colOthers_inv {t : Array UInt64} {L : Layout} {B : Finset Nat} (hL : L.Good)
    (hs : Static t L) (h : Cols t L B (L.present B)) {i : Nat} (j : Nat) :
    let l := colList (L.colQ (L.present B) i)
    Static (delAll (colOthers L (l.take j)) t) L ∧
      Cols (delAll (colOthers L (l.take j)) t) L B
        (L.present B \ (colOthers L (l.take j)).toFinset) ∧
      L.colQ (L.present B \ (colOthers L (l.take j)).toFinset) i = L.colQ (L.present B) i := by
  intro l
  have hsub : ∀ r ∈ l, r ∈ L.colQ (L.present B) i := fun r hr => mem_colList.mp hr
  obtain ⟨hnd, hq⟩ := colOthers_facts hL l (colList_nodup _) hsub
  have hpre := colOthers_prefix L l j
  obtain ⟨hs', hc'⟩ := delAll_inv _ t _ hs h (hnd.sublist hpre.sublist)
    fun q hq' => ⟨(hq q (hpre.subset hq')).1, (hq q (hpre.subset hq')).2.1⟩
  refine ⟨hs', hc', ?_⟩
  ext y
  simp only [Layout.colQ, mem_filter, mem_sdiff, List.mem_toFinset]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hyP, hyi⟩
    refine ⟨⟨hyP, fun hy => ?_⟩, hyi⟩
    exact (hq y (hpre.subset hy)).2.2 hyi

/-- `hideColumn i` hides the options of column `i` from the top down. -/
theorem hideColumn_eq {t : Array UInt64} {L : Layout} {B : Finset Nat} (hL : L.Good)
    (hs : Static t L) (h : Cols t L B (L.present B)) {i : UInt64} (hi : i.toNat ∈ B) :
    hideColumn i t = delAll (colOthers L (colList (L.colQ (L.present B) i.toNat))) t := by
  set Q := L.colQ (L.present B) i.toNat with hQ
  have hlen := colList_length Q
  have hnd := colList_nodup Q
  have hsize : t.size < 2 ^ 60 := by rw [hs.size]; exact hL.small
  have hcolt : Col t i.toNat Q := h.col _ hi
  have hA := hcolt.above
  have hiS := hcolt.size _ (mem_insert_self _ _)
  have hcard : Q.card < t.size := by
    have hsub : insert i.toNat Q ⊆ range t.size := by
      intro z hz
      have := hcolt.size z hz
      exact mem_range.mpr (by omega)
    have := card_le_card hsub
    rw [card_insert_of_notMem (fun hm => Nat.lt_irrefl _ (hA _ hm)), card_range] at this
    omega
  let Inv : UInt64 × Array UInt64 → Prop := fun s => ∃ j ≤ (colList Q).length,
    s.1.toNat = (if h : j < (colList Q).length then (colList Q)[j] else i.toNat) ∧
      s.2 = delAll (colOthers L ((colList Q).take j)) t
  let μ : UInt64 × Array UInt64 → Nat := fun s =>
    if s.1.toNat = i.toNat then 0 else (colList Q).length - (colList Q).idxOf s.1.toNat
  have hμle : ∀ s, μ s ≤ (colList Q).length := fun s => by
    show (if _ then _ else _) ≤ _
    split
    · exact Nat.zero_le _
    · exact Nat.sub_le _ _
  have hfuel : μ (t[(3 * i + 2).toNat]!, t) < t.size.toUInt64.toNat := by
    have := hμle (t[(3 * i + 2).toNat]!, t)
    rw [size_toUInt64 t (by omega)]
    omega
  have hinit : Inv (t[(3 * i + 2).toNat]!, t) := by
    refine ⟨0, Nat.zero_le _, ?_, by simp [delAll, colOthers]⟩
    show (t[(3 * i + 2).toNat]!).toNat = _
    obtain ⟨-, -, e2⟩ := idx3 i (by omega)
    rw [e2, ← W, hcolt.down _ (mem_insert_self _ _), nxt_head_colList hA]
  unfold hideColumn
  dsimp only
  refine repeatWhile_of_inv _ _ _ _ Inv μ
    (fun s => s.2 = delAll (colOthers L (colList Q)) t) hinit hfuel ?_ ?_
  rotate_left
  all_goals clear hinit hfuel
  · rintro ⟨r, t'⟩ ⟨j, hj, hr, ht⟩ hc
    simp only [decide_eq_false_iff_not, not_not] at hc
    dsimp only at hr ht hc ⊢
    have hjl : j = (colList Q).length := by
      by_contra hne
      have hlt : j < (colList Q).length := by omega
      rw [dite_eq_left hlt, hc] at hr
      have := hA _ (mem_colList.mp (List.getElem_mem hlt))
      omega
    rw [ht, hjl, List.take_length]
  · rintro ⟨r, t'⟩ ⟨j, hj, hr, ht⟩ hcond
    simp only [ne_eq, decide_eq_true_eq] at hcond
    dsimp only at hr ht ⊢
    have hlt : j < (colList Q).length := by
      by_contra hne
      rw [dite_eq_right hne] at hr
      exact hcond (UInt64.toNat_inj.mp hr)
    rw [dite_eq_left hlt] at hr
    have hrQ : r.toNat ∈ Q := by rw [hr]; exact mem_colList.mp (List.getElem_mem hlt)
    obtain ⟨hs', hc', hQ'⟩ := colOthers_inv hL hs h (i := i.toNat) j
    obtain ⟨hs'', hc'', hQ''⟩ := colOthers_inv hL hs h (i := i.toNat) (j + 1)
    have hrn : L.IsNode r.toNat := (mem_filter.mp (colQ_node hrQ).1).2.1
    have hat := Layout.at_of_isNode hrn
    obtain ⟨hnd', hq⟩ := colOthers_facts hL (colList Q) hnd fun r hr => mem_colList.mp hr
    have hpre := colOthers_prefix L (colList Q) (j + 1)
    have hsplit := colOthers_take_succ L (colList Q) j hlt
    have hoth : ∀ q ∈ L.others (L.optOf r.toNat) (r.toNat - L.first (L.optOf r.toNat)),
        q ∈ L.present B \ (colOthers L ((colList Q).take j)).toFinset ∧ L.nodeItem q ∈ B := by
      intro q hq'
      have hq'' : q ∈ colOthers L ((colList Q).take (j + 1)) := by
        rw [hsplit, ← hr]; exact List.mem_append_right _ hq'
      refine ⟨mem_sdiff.mpr ⟨(hq q (hpre.subset hq'')).1, ?_⟩, (hq q (hpre.subset hq'')).2.1⟩
      intro hin
      have hnd2 := hnd'.sublist hpre.sublist
      rw [hsplit] at hnd2
      exact List.disjoint_of_nodup_append hnd2 (List.mem_toFinset.mp hin)
        (by rw [← hr]; exact hq')
    have hhide : hide r t' = delAll (colOthers L ((colList Q).take (j + 1))) t := by
      rw [ht, hide_eq hL hs' hc' hat hoth, hsplit, delAll_append]
      unfold Layout.oth
      rw [hr]
    have hcol'' : Col (delAll (colOthers L ((colList Q).take (j + 1))) t) i.toNat Q := by
      have := hc''.col _ hi; rwa [hQ''] at this
    have hsz : (delAll (colOthers L ((colList Q).take (j + 1))) t).size = t.size := delAll_size _ _
    obtain ⟨-, -, e2⟩ := idx3 r (by have := hcol''.size _ (mem_insert_of_mem hrQ); omega)
    have hnext : ((hide r t')[(3 * r + 2).toNat]!).toNat =
        (if h : j + 1 < (colList Q).length then (colList Q)[j + 1] else i.toNat) := by
      rw [hhide, e2, ← W, hcol''.down _ (mem_insert_of_mem hrQ), hr, nxt_colList j hlt]
    have hidx : ∀ j' (hj' : j' < (colList Q).length), (colList Q).idxOf (colList Q)[j'] = j' :=
      fun j' hj' => List.Nodup.idxOf_getElem hnd j' hj'
    refine ⟨⟨j + 1, by omega, hnext, hhide⟩, ?_⟩
    show (if _ then _ else _) < (if _ then _ else _)
    rw [hnext, hr]
    have hne : (colList Q)[j] ≠ i.toNat := Nat.ne_of_gt (hA _ (mem_colList.mp (List.getElem_mem hlt)))
    rw [ite_eq_right hne, hidx j hlt]
    by_cases h1 : j + 1 < (colList Q).length
    · have hne1 : (colList Q)[j + 1] ≠ i.toNat :=
        Nat.ne_of_gt (hA _ (mem_colList.mp (List.getElem_mem h1)))
      rw [dite_eq_left h1, ite_eq_right hne1, hidx (j + 1) h1]
      omega
    · rw [dite_eq_right h1, ite_eq_left rfl]
      omega

/-- `unhideColumn i`, applied to the array that `hideColumn i` leaves, returns the array before
`hideColumn`. -/
theorem unhideColumn_eq {t : Array UInt64} {L : Layout} {B : Finset Nat} (hL : L.Good)
    (hs : Static t L) (h : Cols t L B (L.present B)) {i : UInt64} (hi : i.toNat ∈ B) :
    unhideColumn i (delAll (colOthers L (colList (L.colQ (L.present B) i.toNat))) t) = t := by
  set Q := L.colQ (L.present B) i.toNat with hQ
  have hnd := colList_nodup Q
  have hsize : t.size < 2 ^ 60 := by rw [hs.size]; exact hL.small
  have hA : Above i.toNat Q := (h.col _ hi).above
  obtain ⟨hsL, hcL, hQL⟩ := colOthers_inv hL hs h (i := i.toNat) (colList Q).length
  rw [List.take_length] at hsL hcL hQL
  have hcolL : Col (delAll (colOthers L (colList Q)) t) i.toNat Q := by
    have := hcL.col _ hi; rwa [hQL] at this
  have hiS := hcolL.size _ (mem_insert_self _ _)
  have hlen_lt : (colList Q).length < t.size := by
    rw [colList_length]
    by_contra hge
    push Not at hge
    have hsub : insert i.toNat Q ⊆ range t.size := by
      intro z hz
      have := hcolL.size z hz
      rw [delAll_size] at this
      exact mem_range.mpr (by omega)
    have := card_le_card hsub
    rw [card_insert_of_notMem (fun hm => Nat.lt_irrefl _ (hA _ hm)), card_range] at this
    omega
  let Inv : UInt64 × Array UInt64 → Prop := fun s => ∃ j ≤ (colList Q).length,
    s.1.toNat = (if h : 0 < j ∧ j ≤ (colList Q).length then (colList Q)[j - 1]'(by omega)
      else i.toNat) ∧
      s.2 = delAll (colOthers L ((colList Q).take j)) t
  let μ : UInt64 × Array UInt64 → Nat := fun s =>
    if s.1.toNat = i.toNat then 0 else (colList Q).idxOf s.1.toNat + 1
  set T := delAll (colOthers L (colList Q)) t with hT
  have hidx : ∀ j' (hj' : j' < (colList Q).length), (colList Q).idxOf (colList Q)[j'] = j' :=
    fun j' hj' => List.Nodup.idxOf_getElem hnd j' hj'
  have he1 : (T[(3 * i + 1).toNat]!).toNat =
      (if h : 0 < (colList Q).length then (colList Q)[(colList Q).length - 1] else i.toNat) := by
    obtain ⟨-, e1, -⟩ := idx3 i (by rw [delAll_size] at hiS; omega)
    rw [e1, ← W, hcolL.up _ (mem_insert_self _ _), prv_head_colList]
  have hfuel : μ (T[(3 * i + 1).toNat]!, T) < T.size.toUInt64.toNat := by
    show (if _ then _ else _) < _
    rw [he1, size_toUInt64 T (by rw [hT, delAll_size]; omega), hT, delAll_size]
    by_cases h0 : 0 < (colList Q).length
    · have hne : (colList Q)[(colList Q).length - 1] ≠ i.toNat :=
        Nat.ne_of_gt (hA _ (mem_colList.mp (List.getElem_mem (by omega))))
      rw [dite_eq_left h0, ite_eq_right hne, hidx _ (by omega)]
      omega
    · rw [dite_eq_right h0, ite_eq_left rfl]
      omega
  have hinit : Inv (T[(3 * i + 1).toNat]!, T) := by
    refine ⟨(colList Q).length, le_rfl, ?_, by rw [List.take_length]⟩
    show (T[(3 * i + 1).toNat]!).toNat = _
    rw [he1]
    by_cases h0 : 0 < (colList Q).length
    · rw [dite_eq_left h0, dite_eq_left ⟨h0, le_rfl⟩]
    · rw [dite_eq_right h0, dite_eq_right (fun h => h0 h.1)]
  unfold unhideColumn
  dsimp only
  refine repeatWhile_of_inv _ _ _ _ Inv μ (fun s => s.2 = t) hinit hfuel ?_ ?_
  rotate_left
  all_goals clear hinit hfuel
  · rintro ⟨r, t'⟩ ⟨j, hj, hr, ht⟩ hc
    simp only [decide_eq_false_iff_not, not_not] at hc
    dsimp only at hr ht hc ⊢
    have hj0 : j = 0 := by
      by_contra hne
      have hpos : 0 < j := Nat.pos_of_ne_zero hne
      rw [dite_eq_left ⟨hpos, hj⟩, hc] at hr
      have := hA _ (mem_colList.mp (List.getElem_mem (show j - 1 < (colList Q).length by omega)))
      omega
    rw [ht, hj0]
    rfl
  · rintro ⟨r, t'⟩ ⟨j, hj, hr, ht⟩ hcond
    simp only [ne_eq, decide_eq_true_eq] at hcond
    dsimp only at hr ht ⊢
    have hpos : 0 < j := by
      by_contra hne
      rw [dite_eq_right (fun h => hne h.1)] at hr
      exact hcond (UInt64.toNat_inj.mp hr)
    rw [dite_eq_left ⟨hpos, hj⟩] at hr
    have hlt : j - 1 < (colList Q).length := by omega
    have hrQ : r.toNat ∈ Q := by rw [hr]; exact mem_colList.mp (List.getElem_mem hlt)
    obtain ⟨hs', hc', hQ'⟩ := colOthers_inv hL hs h (i := i.toNat) (j - 1)
    have hrn : L.IsNode r.toNat := (mem_filter.mp (colQ_node hrQ).1).2.1
    have hat := Layout.at_of_isNode hrn
    obtain ⟨hnd', hq⟩ := colOthers_facts hL (colList Q) hnd fun r hr => mem_colList.mp hr
    have hj1 : j - 1 + 1 = j := by omega
    have hpre := colOthers_prefix L (colList Q) j
    have hsplit := colOthers_take_succ L (colList Q) (j - 1) hlt
    rw [hj1] at hsplit
    have hoth : ∀ q ∈ L.others (L.optOf r.toNat) (r.toNat - L.first (L.optOf r.toNat)),
        q ∈ L.present B \ (colOthers L ((colList Q).take (j - 1))).toFinset ∧
          L.nodeItem q ∈ B := by
      intro q hq'
      have hq'' : q ∈ colOthers L ((colList Q).take j) := by
        rw [hsplit, ← hr]; exact List.mem_append_right _ hq'
      refine ⟨mem_sdiff.mpr ⟨(hq q (hpre.subset hq'')).1, ?_⟩, (hq q (hpre.subset hq'')).2.1⟩
      intro hin
      have hnd2 := hnd'.sublist hpre.sublist
      rw [hsplit] at hnd2
      exact List.disjoint_of_nodup_append hnd2 (List.mem_toFinset.mp hin)
        (by rw [← hr]; exact hq')
    have hunhide : unhide r t' = delAll (colOthers L ((colList Q).take (j - 1))) t := by
      rw [ht, hsplit, delAll_append]
      have := unhide_eq hL hs' hc' hat hoth
      unfold Layout.oth
      rw [← hr]
      exact this
    have hcol' : Col (delAll (colOthers L ((colList Q).take (j - 1))) t) i.toNat Q := by
      have := hc'.col _ hi; rwa [hQ'] at this
    obtain ⟨-, e1, -⟩ := idx3 r (by
      have := hcol'.size _ (mem_insert_of_mem hrQ)
      rw [delAll_size] at this; omega)
    have hnext : ((unhide r t')[(3 * r + 1).toNat]!).toNat =
        (if h : 0 < j - 1 ∧ j - 1 ≤ (colList Q).length then (colList Q)[j - 1 - 1]'(by omega)
          else i.toNat) := by
      rw [hunhide, e1, ← W, hcol'.up _ (mem_insert_of_mem hrQ), hr, prv_colList hA (j - 1) hlt]
      by_cases h1 : 0 < j - 1
      · rw [dite_eq_left h1, dite_eq_left ⟨h1, by omega⟩]
      · rw [dite_eq_right h1, dite_eq_right (fun h => h1 h.1)]
    refine ⟨⟨j - 1, by omega, hnext, hunhide⟩, ?_⟩
    show (if _ then _ else _) < (if _ then _ else _)
    rw [hnext, hr]
    have hne : (colList Q)[j - 1] ≠ i.toNat := Nat.ne_of_gt (hA _ (mem_colList.mp (List.getElem_mem hlt)))
    rw [ite_eq_right hne, hidx (j - 1) hlt]
    by_cases h1 : 0 < j - 1
    · have hlt1 : j - 1 - 1 < (colList Q).length := by omega
      have hne1 : (colList Q)[j - 1 - 1] ≠ i.toNat :=
        Nat.ne_of_gt (hA _ (mem_colList.mp (List.getElem_mem hlt1)))
      rw [dite_eq_left ⟨h1, by omega⟩, ite_eq_right hne1, hidx (j - 1 - 1) hlt1]
      omega
    · rw [dite_eq_right (fun h => h1 h.1), ite_eq_left rfl]
      omega

end Library.Combinatorics.DancingLinks
