import Library.Combinatorics.DancingLinks.Cover

/-! Steps X5 and X6 for one option, and step X3.  `coverOthers b r` walks the option of node `r`
forward from `r + 1` and covers the item of each node, and `uncoverOthers b r` walks it backward
from `r - 1` and uncovers them, so both are walks of `Walk.lean` with `coverItem` and
`uncoverItem` as the operation.  `coverFold_inv` shows that covering the items of the nodes of a
list keeps the invariant of the remaining items, from `cover_inv`, so `coverOthers_eq` and
`uncoverOthers_eq` follow from `walkFwd` and `walkBwd`.  `choose_mem` shows that `choose`
returns an active item when one exists: it walks the list of active items, and the item it keeps
is always one of them.  Which active item it returns does not affect the count. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

/-- Covering the item of node `q`. -/
def coverNode (L : Layout) (b : UInt64) (q : Nat) (t : Array UInt64) : Array UInt64 :=
  coverItem b (UInt64.ofNat (L.nodeItem q)) t

/-- The items of the nodes of `l`. -/
def itemsOf (L : Layout) (l : List Nat) : Finset Nat := (l.map L.nodeItem).toFinset

theorem coverFold_inv {L : Layout} (hL : L.Good) {b : UInt64} (hb : b.toNat = L.base) :
    ∀ (l : List Nat) (t : Array UInt64) (B : Finset Nat), Inv t L B →
      (l.map L.nodeItem).Nodup → (∀ q ∈ l, L.nodeItem q ∈ B) →
      Inv (gfold (coverNode L b) l t) L (B \ itemsOf L l)
  | [], t, B, h, _, _ => by simpa [gfold, itemsOf] using h
  | q :: l, t, B, h, hnd, hl => by
    have hqB := hl q List.mem_cons_self
    have hsmall : L.nodeItem q < 2 ^ 64 := by
      have := (h.sub _ hqB).2; have := hL.small; omega
    have hto : (UInt64.ofNat (L.nodeItem q)).toNat = L.nodeItem q :=
      UInt64.toNat_ofNat_of_lt' hsmall
    obtain ⟨h1, -, -⟩ := cover_inv hL h hb (i := UInt64.ofNat (L.nodeItem q)) (by rw [hto]; exact hqB)
    rw [hto] at h1
    rw [List.map_cons] at hnd
    have hnd' := List.nodup_cons.mp hnd
    have := coverFold_inv hL hb l (coverNode L b q t) (B.erase (L.nodeItem q)) h1
      hnd'.2 (fun q' hq' => mem_erase.mpr ⟨fun e => hnd'.1 (List.mem_map.mpr ⟨q', hq', e⟩),
        hl q' (List.mem_cons_of_mem _ hq')⟩)
    have hset : B.erase (L.nodeItem q) \ itemsOf L l = B \ itemsOf L (q :: l) := by
      ext y; simp only [itemsOf, mem_sdiff, mem_erase, List.map_cons, List.toFinset_cons,
        mem_insert, List.mem_toFinset]
      tauto
    rw [← hset]
    exact this

/-- The words that a cover leaves at the `TOP` of a node: its item. -/
theorem top_word {t : Array UInt64} {L : Layout} (hL : L.Good) (hs : Static t L) {q : UInt64}
    {k m : Nat} (hat : L.At q.toNat k m) :
    t[(3 * q).toNat]! = UInt64.ofNat (L.nodeItem q.toNat) := by
  have hsize : t.size < 2 ^ 60 := by rw [hs.size]; exact hL.small
  have hlast := L.first_le_last hat.1
  rw [Layout.first_succ] at hlast
  have hbase : 3 * L.first L.os.length ≤ t.size := by rw [hs.size, Layout.base]; omega
  have hm := hat.2.1
  obtain ⟨e0, -, -⟩ := idx3 q (by have := hat.2.2; omega)
  rw [e0, Layout.nodeItem_at hat, ← hs.top _ hat.1 _ hat.2.1, ← hat.2.2, W, UInt64.ofNat_toNat]

/-- The items of the nodes of `others` are the other items of the option. -/
theorem others_items {L : Layout} (hL : L.Good) {k m : Nat} (hk : k < L.os.length)
    (hm : m < L.len k) :
    ((L.others k m).map L.nodeItem).Nodup ∧
      itemsOf L (L.others k m) = (L.os[k]!).toFinset.erase (L.item k m) := by
  have hnd := hL.nodup k hk
  have hmem : ∀ q ∈ L.others k m, L.At q k (q - L.first k) := by
    intro q hq
    obtain ⟨m', hm', _, rfl⟩ := (Layout.mem_others hm).mp hq
    exact ⟨hk, by omega, by omega⟩
  refine ⟨?_, ?_⟩
  · refine (List.nodup_map_iff_inj_on (L.others_nodup k m)).mpr fun x hx y hy hxy => ?_
    rw [Layout.nodeItem_at (hmem x hx), Layout.nodeItem_at (hmem y hy)] at hxy
    exact Layout.node_eq_of_item hL (hmem x hx) (hmem y hy) hxy
  · ext j
    simp only [itemsOf, List.mem_toFinset, List.mem_map, mem_erase]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨m', hm', hne, rfl⟩ := (Layout.mem_others hm).mp hq
      have hat : L.At (L.first k + m') k m' := ⟨hk, hm', rfl⟩
      rw [Layout.nodeItem_at hat]
      refine ⟨fun he => hne ?_, ?_⟩
      · have := Layout.node_eq_of_item hL hat ⟨hk, hm, rfl⟩ he
        omega
      · unfold Layout.item
        have hm'l : m' < (L.os[k]!).length := hm'
        rw [getElem!_pos _ m' hm'l]
        exact List.getElem_mem _
    · rintro ⟨hne, hj⟩
      obtain ⟨m', hm', he⟩ := List.getElem_of_mem hj
      have hat : L.At (L.first k + m') k m' := ⟨hk, hm', rfl⟩
      have hitem : L.item k m' = j := by
        unfold Layout.item; rw [getElem!_pos _ m' hm']; exact he
      refine ⟨L.first k + m', (Layout.mem_others hm).mpr ⟨m', hm', fun e => hne ?_, rfl⟩, ?_⟩
      · rw [← hitem, e]
      · rw [Layout.nodeItem_at hat, hitem]

/-- `coverOthers b r` covers the other items of the option of node `r`. -/
theorem coverOthers_eq {t : Array UInt64} {L : Layout} {B : Finset Nat} (hL : L.Good)
    {b : UInt64} (hb : b.toNat = L.base) (h : Inv t L B) {r : UInt64} {k m : Nat}
    (hat : L.At r.toNat k m) (hin : ∀ j ∈ (L.os[k]!).toFinset.erase (L.item k m), j ∈ B) :
    coverOthers b r t = gfold (coverNode L b) (L.others k m) t ∧
      Inv (coverOthers b r t) L (B \ ((L.os[k]!).toFinset.erase (L.item k m))) := by
  obtain ⟨hnd, hitems⟩ := others_items hL hat.1 hat.2.1
  have hall : ∀ q ∈ L.others k m, L.nodeItem q ∈ B := fun q hq =>
    hin _ (by rw [← hitems]; exact List.mem_toFinset.mpr (List.mem_map_of_mem hq))
  have hpre : ∀ l, l <+: L.others k m → Inv (gfold (coverNode L b) l t) L (B \ itemsOf L l) :=
    fun l hl => coverFold_inv hL hb l t B h (hnd.sublist (hl.sublist.map _))
      fun q hq => hall q (hl.subset hq)
  have heq : coverOthers b r t = gfold (coverNode L b) (L.others k m) t := by
    unfold coverOthers
    dsimp only
    refine walkFwd hL hat (fun q t => coverItem b t[(3 * q).toNat]! t) (coverNode L b) t
      (fun l hl => (hpre l hl).static) (fun l q hl => ?_)
    have hq : q.toNat ∈ L.others k m := hl.subset (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨m', hm', _, e⟩ := (Layout.mem_others hat.2.1).mp hq
    have hatq : L.At q.toNat k m' := ⟨hat.1, hm', e⟩
    show coverItem b _ _ = coverItem b _ _
    rw [top_word hL (hpre l ((List.prefix_append l _).trans hl)).static hatq]
  refine ⟨heq, ?_⟩
  rw [heq, ← hitems]
  exact hpre _ (List.prefix_refl _)

/-- `uncoverOthers b r`, applied to the array that `coverOthers b r` leaves, returns the array
before. -/
theorem uncoverOthers_eq {t : Array UInt64} {L : Layout} {B : Finset Nat} (hL : L.Good)
    {b : UInt64} (hb : b.toNat = L.base) (h : Inv t L B) {r : UInt64} {k m : Nat}
    (hat : L.At r.toNat k m) (hin : ∀ j ∈ (L.os[k]!).toFinset.erase (L.item k m), j ∈ B) :
    uncoverOthers b r (coverOthers b r t) = t := by
  obtain ⟨hnd, hitems⟩ := others_items hL hat.1 hat.2.1
  have hall : ∀ q ∈ L.others k m, L.nodeItem q ∈ B := fun q hq =>
    hin _ (by rw [← hitems]; exact List.mem_toFinset.mpr (List.mem_map_of_mem hq))
  have hpre : ∀ l, l <+: L.others k m → Inv (gfold (coverNode L b) l t) L (B \ itemsOf L l) :=
    fun l hl => coverFold_inv hL hb l t B h (hnd.sublist (hl.sublist.map _))
      fun q hq => hall q (hl.subset hq)
  rw [(coverOthers_eq hL hb h hat hin).1]
  unfold uncoverOthers
  dsimp only
  refine walkBwd hL hat (fun q t => uncoverItem b t[(3 * q).toNat]! t) (coverNode L b) t
    (fun l hl => (hpre l hl).static) (fun l q hl => ?_)
  have hq : q.toNat ∈ L.others k m := hl.subset (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨m', hm', _, e⟩ := (Layout.mem_others hat.2.1).mp hq
  have hatq : L.At q.toNat k m' := ⟨hat.1, hm', e⟩
  have hl' : l <+: L.others k m := (List.prefix_append l _).trans hl
  have hX := hpre l hl'
  have hqB : L.nodeItem q.toNat ∈ B \ itemsOf L l := by
    refine mem_sdiff.mpr ⟨hall _ hq, fun hin' => ?_⟩
    have hnd2 := (hnd.sublist (hl.sublist.map L.nodeItem))
    rw [List.map_append] at hnd2
    exact List.disjoint_of_nodup_append hnd2 (List.mem_toFinset.mp hin')
      (List.mem_singleton_self _)
  have hsmall : L.nodeItem q.toNat < 2 ^ 64 := by
    have := (hX.sub _ hqB).2; have := hL.small; omega
  have hto : (UInt64.ofNat (L.nodeItem q.toNat)).toNat = L.nodeItem q.toNat :=
    UInt64.toNat_ofNat_of_lt' hsmall
  obtain ⟨h1, h2, -⟩ := cover_inv hL hX hb (i := UInt64.ofNat (L.nodeItem q.toNat))
    (by rw [hto]; exact hqB)
  show uncoverItem b _ (gfold (coverNode L b) (l ++ [q.toNat]) t) = _
  rw [gfold_concat, show coverNode L b q.toNat (gfold (coverNode L b) l t) =
    coverItem b (UInt64.ofNat (L.nodeItem q.toNat)) (gfold (coverNode L b) l t) from rfl,
    top_word hL h1.static hatq]
  exact h2

/-- `choose` returns an active item when one exists. -/
theorem choose_mem {t : Array UInt64} {L : Layout} {B : Finset Nat} (hL : L.Good)
    {b : UInt64} (hb : b.toNat = L.base) (h : Inv t L B) (hne : B.Nonempty) :
    (choose b t).toNat ∈ B := by
  have hA : Above 0 B := fun c hc => (h.sub c hc).1
  have hsize : t.size = L.base + 2 * (L.n + 1) := h.static.size
  have hsmall := hL.small
  have hnd := colList_nodup B
  have hlen : (colList B).length = B.card := colList_length B
  have hpos : 0 < (colList B).length := by rw [hlen]; exact card_pos.mpr hne
  have hbound : ∀ y ∈ insert 0 B, y ≤ L.n := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · omega
    · exact (h.sub y hy).2
  have hidx : ∀ j' (hj' : j' < (colList B).length), (colList B).idxOf (colList B)[j'] = j' :=
    fun j' hj' => List.Nodup.idxOf_getElem hnd j' hj'
  have hcard : B.card ≤ L.n := by
    have : B ⊆ Finset.Icc 1 L.n := fun c hc => Finset.mem_Icc.mpr (h.sub c hc)
    have := card_le_card this
    simp at this; omega
  have hread : ∀ y ∈ insert 0 B, (t[(b + 2 * UInt64.ofNat y + 1).toNat]!).toNat = nxt 0 B y := by
    intro y hy
    have hy' := hbound y hy
    have hto : (UInt64.ofNat y).toNat = y := UInt64.toNat_ofNat_of_lt' (show y < 2 ^ 64 by omega)
    obtain ⟨-, e⟩ := idx_item b (UInt64.ofNat y) (by rw [hto]; omega)
    rw [e, hto, hb, ← W]
    exact h.items.right y hy
  let Inv' : UInt64 × UInt64 × UInt64 → Prop := fun s => ∃ j ≤ (colList B).length,
    s.1.toNat = (if h : j < (colList B).length then (colList B)[j] else 0) ∧
      (j = 0 → s.2.1 = 0) ∧ (0 < j → s.2.1.toNat ∈ B)
  let μ : UInt64 × UInt64 × UInt64 → Nat := fun s =>
    if s.1.toNat = 0 then 0 else (colList B).length - (colList B).idxOf s.1.toNat
  have hμle : ∀ s, μ s ≤ (colList B).length := fun s => by
    show (if _ then _ else _) ≤ _
    split
    · exact Nat.zero_le _
    · exact Nat.sub_le _ _
  have hfuel : μ (t[(b + 1).toNat]!, 0, 0) < t.size.toUInt64.toNat := by
    have := hμle (t[(b + 1).toNat]!, 0, 0)
    rw [size_toUInt64 t (by omega)]
    omega
  have hinit : Inv' (t[(b + 1).toNat]!, 0, 0) := by
    refine ⟨0, Nat.zero_le _, ?_, fun _ => rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩
    show (t[(b + 1).toNat]!).toNat = _
    have := hread 0 (mem_insert_self 0 B)
    have e0 : b + 2 * UInt64.ofNat 0 + 1 = b + 1 := UInt64.toNat_inj.mp (by
      simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
      omega)
    rw [e0] at this
    rw [this, nxt_head_colList hA]
  unfold choose
  dsimp only
  refine repeatWhile_of_inv _ _ _ _ Inv' μ (fun s => s.2.1.toNat ∈ B) hinit hfuel ?_ ?_
  rotate_left
  all_goals clear hinit hfuel
  · rintro ⟨p, best, len⟩ ⟨j, hj, hp, h0, h1⟩ hc
    simp only [decide_eq_false_iff_not, not_not] at hc
    dsimp only at hp h0 h1 hc ⊢
    have hjl : j = (colList B).length := by
      by_contra hne'
      have hlt : j < (colList B).length := by omega
      rw [dite_eq_left hlt, hc] at hp
      have := hA _ (mem_colList.mp (List.getElem_mem hlt))
      simp at hp; omega
    exact h1 (by omega)
  · rintro ⟨p, best, len⟩ ⟨j, hj, hp, h0, h1⟩ hcond
    simp only [ne_eq, decide_eq_true_eq] at hcond
    dsimp only at hp h0 h1 ⊢
    have hlt : j < (colList B).length := by
      by_contra hne'
      rw [dite_eq_right hne'] at hp
      exact hcond (UInt64.toNat_inj.mp (by rw [hp]; rfl))
    rw [dite_eq_left hlt] at hp
    have hpB : p.toNat ∈ B := by rw [hp]; exact mem_colList.mp (List.getElem_mem hlt)
    have hp' : p = UInt64.ofNat p.toNat := (UInt64.ofNat_toNat).symm
    have hnext : (t[(b + 2 * p + 1).toNat]!).toNat =
        (if h : j + 1 < (colList B).length then (colList B)[j + 1] else 0) := by
      have := hread p.toNat (mem_insert_of_mem hpB)
      rw [← hp'] at this
      rw [this, hp, nxt_colList j hlt]
    refine ⟨⟨j + 1, by omega, hnext, fun e => absurd e (Nat.succ_ne_zero j), fun _ => ?_⟩, ?_⟩
    · split
      · exact hpB
      · rename_i hb'
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · exact absurd (Or.inl (h0 hj0)) hb'
        · exact h1 hj0
    · show (if _ then _ else _) < (if _ then _ else _)
      rw [hnext, hp]
      have hne0 : (colList B)[j] ≠ 0 := Nat.ne_of_gt (hA _ (mem_colList.mp (List.getElem_mem hlt)))
      rw [ite_eq_right hne0, hidx j hlt]
      by_cases h1' : j + 1 < (colList B).length
      · have hne1 : (colList B)[j + 1] ≠ 0 :=
          Nat.ne_of_gt (hA _ (mem_colList.mp (List.getElem_mem h1')))
        rw [dite_eq_left h1', ite_eq_right hne1, hidx (j + 1) h1']
        omega
      · rw [dite_eq_right h1', ite_eq_left rfl]
        omega

end Library.Combinatorics.DancingLinks
