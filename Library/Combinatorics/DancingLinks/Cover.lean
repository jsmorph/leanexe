import Library.Combinatorics.DancingLinks.Column

/-! Knuth's `cover(i)` and `uncover(i)` on the whole array.  The item links follow the nodes, at
`base = 3(Z + 1)`: `Items t L B` states that `LLINK` and `RLINK` give each item of `B ∪ {0}` its
predecessor and successor among them in increasing order, with item 0 as the header, the same
cyclic order as a column's.  `Inv t L B` is the invariant of the search: the static words, the
items `B` in `1..N`, the list of active items, and the column of each active item with the nodes of
the options that lie inside `B`.  `cover_inv` shows that `coverItem i` leaves `Inv` of `B` without
`i`, that `uncoverItem i` undoes it, and that the column of `i` keeps its links.  Removals write
only words below `base`, and the item operations only words from `base` on, so each leaves the
other's facts alone. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

/-- The list of active items `B`, with item 0 as its header. -/
structure Items (t : Array UInt64) (L : Layout) (B : Finset Nat) : Prop where
  left : ∀ y ∈ insert 0 B, W t (L.base + 2 * y) = prv 0 B y
  right : ∀ y ∈ insert 0 B, W t (L.base + 2 * y + 1) = nxt 0 B y

/-- The invariant of the search for the active items `B`. -/
structure Inv (t : Array UInt64) (L : Layout) (B : Finset Nat) : Prop where
  static : Static t L
  sub : ∀ c ∈ B, 1 ≤ c ∧ c ≤ L.n
  items : Items t L B
  cols : Cols t L B (L.present B)

/-- The words of the nodes lie below `base`. -/
theorem node_words_lt {L : Layout} {y : Nat} (hy : y ≤ L.n ∨ L.IsNode y) (r : Nat) (hr : r < 3) :
    3 * y + r < L.base := by
  unfold Layout.base
  rcases hy with hy | hy
  · have := L.n_lt_first L.os.length; omega
  · have := (L.node_lt hy).2; omega

/-- A removal leaves the item links. -/
theorem Items.del {t : Array UInt64} {L : Layout} {B C P : Finset Nat} (hi : Items t L B)
    (h : Cols t L C P) {q : Nat} (hq : q ∈ P) (hc : L.nodeItem q ∈ C) :
    Items (DancingLinks.del t q) L B := by
  have hw := del_writes h hq hc
  have key : ∀ k, L.base ≤ k → (DancingLinks.del t q)[k]! = t[k]! := fun k hk =>
    hw k fun y hy r hr _ => by have := node_words_lt hy r hr; omega
  exact ⟨fun y hy => by rw [W, key _ (by omega)]; exact hi.left y hy,
    fun y hy => by rw [W, key _ (by omega)]; exact hi.right y hy⟩

theorem Items.delAll {L : Layout} {C : Finset Nat} {B : Finset Nat} :
    ∀ (l : List Nat) (t : Array UInt64) (P : Finset Nat), Items t L B → Cols t L C P → l.Nodup →
      (∀ q ∈ l, q ∈ P ∧ L.nodeItem q ∈ C) → Items (DancingLinks.delAll l t) L B
  | [], _, _, hi, _, _, _ => hi
  | q :: l, t, P, hi, h, hnd, hl => by
    obtain ⟨hqP, hqC⟩ := hl q List.mem_cons_self
    have hl' : ∀ q' ∈ l, q' ∈ P.erase q ∧ L.nodeItem q' ∈ C := by
      intro q' hq'
      obtain ⟨h1, h2⟩ := hl q' (List.mem_cons_of_mem _ hq')
      refine ⟨mem_erase.mpr ⟨?_, h1⟩, h2⟩
      rintro rfl
      exact (List.nodup_cons.mp hnd).1 hq'
    exact Items.delAll l (DancingLinks.del t q) (P.erase q) (hi.del h hqP hqC) (h.del hqP hqC)
      (List.nodup_cons.mp hnd).2 hl'

/-- An array that agrees with `t` below `base` keeps the static words and the columns. -/
theorem below_base {t t' : Array UInt64} {L : Layout} {C P : Finset Nat} (hs : Static t L)
    (h : Cols t L C P) (hsz : t'.size = t.size) (hk : ∀ k < L.base, t'[k]! = t[k]!) :
    Static t' L ∧ Cols t' L C P := by
  have hnode : ∀ k < L.os.length, ∀ m < L.len k, 3 * (L.first k + m) + 2 < L.base := by
    intro k hk' m hm
    have := node_words_lt (Or.inr (L.at_isNode ⟨hk', hm, rfl⟩)) 2 (by omega)
    exact this
  have hsp : ∀ k ≤ L.os.length, 3 * (L.first k - 1) + 2 < L.base := by
    intro k hk'
    unfold Layout.base
    have := L.first_le hk'
    have := L.n_lt_first k
    omega
  refine ⟨⟨by rw [hsz]; exact hs.size, ?_, ?_, ?_, ?_⟩, ⟨h.nodes, h.items, fun c hc => ?_⟩⟩
  · intro k hk' m hm
    rw [W, hk _ (by have := hnode k hk' m hm; omega)]; exact hs.top k hk' m hm
  · intro k hk'
    rw [W, hk _ (by have := hsp k hk'; omega)]; exact hs.spacer k hk'
  · intro k hk'
    rw [W, hk _ (by have := hsp (k + 1) hk'; omega)]; exact hs.up k hk'
  · intro k hk'
    rw [W, hk _ (by have := hsp k (Nat.le_of_lt hk'); omega)]; exact hs.down k hk'
  · refine (h.col c hc).frame hsz fun y hy r hr => hk _ ?_
    apply node_words_lt _ r hr
    rcases mem_insert.mp hy with rfl | hy
    · exact Or.inl (h.items _ hc)
    · exact Or.inr (h.nodes y (colQ_node hy).1)

theorem idx_item (b i : UInt64) (h : b.toNat + 2 * i.toNat + 1 < 2 ^ 64) :
    (b + 2 * i).toNat = b.toNat + 2 * i.toNat ∧ (b + 2 * i + 1).toNat = b.toNat + 2 * i.toNat + 1 := by
  refine ⟨?_, ?_⟩ <;> simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat] <;> omega

/-- The reads of `unlinkItem b i t` for an active item `i`. -/
theorem unlink_get {t : Array UInt64} {L : Layout} {B : Finset Nat} (hs : Static t L)
    (hsub : ∀ c ∈ B, 1 ≤ c ∧ c ≤ L.n) (hi : Items t L B) (hL : L.Good) {b i : UInt64}
    (hb : b.toNat = L.base) (hiB : i.toNat ∈ B) (k : Nat) :
    (unlinkItem b i t)[k]! =
      if k = L.base + 2 * nxt 0 B i.toNat then t[L.base + 2 * i.toNat]!
      else if k = L.base + 2 * prv 0 B i.toNat + 1 then t[L.base + 2 * i.toNat + 1]!
      else t[k]! := by
  have hsize : t.size = L.base + 2 * (L.n + 1) := hs.size
  have hsmall := hL.small
  have hin := (hsub _ hiB).2
  have hl : prv 0 B i.toNat ≤ L.n := by
    rcases prv_mem 0 B i.toNat with h | h
    · omega
    · exact (hsub _ h).2
  have hr : nxt 0 B i.toNat ≤ L.n := by
    rcases nxt_mem 0 B i.toNat with h | h
    · omega
    · exact (hsub _ h).2
  have hiI : i.toNat ∈ insert 0 B := mem_insert_of_mem hiB
  have wl := hi.left _ hiI
  have wr := hi.right _ hiI
  obtain ⟨e1, e2⟩ := idx_item b i (by omega)
  simp only [unlinkItem]
  rw [e1, e2, hb]
  rw [W] at wl wr
  obtain ⟨-, f2⟩ := idx_item b t[L.base + 2 * i.toNat]! (by omega)
  obtain ⟨f1, -⟩ := idx_item b t[L.base + 2 * i.toNat + 1]! (by omega)
  rw [f1, f2, hb, wl, wr, get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
    get_set _ _ _ _ (by omega)]

/-- Removing an active item leaves the list of the other items. -/
theorem unlink_items {t : Array UInt64} {L : Layout} {B : Finset Nat} (hs : Static t L)
    (hsub : ∀ c ∈ B, 1 ≤ c ∧ c ≤ L.n) (hi : Items t L B) (hL : L.Good) {b i : UInt64}
    (hb : b.toNat = L.base) (hiB : i.toNat ∈ B) : Items (unlinkItem b i t) L (B.erase i.toNat) := by
  have hA : Above 0 B := fun c hc => (hsub c hc).1
  have hget := unlink_get hs hsub hi hL hb hiB
  have hsub' : ∀ y ∈ insert 0 (B.erase i.toNat), y ∈ insert 0 B := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_erase.mp hy).2
  have hiI : i.toNat ∈ insert 0 B := mem_insert_of_mem hiB
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · by_cases hyr : y = nxt 0 B i.toNat
    · rw [W, hget, ite_eq_left (by rw [hyr])]
      rw [← W, hi.left _ hiI, hyr]
      exact (prv_erase_nxt hA hiB).symm
    · rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ← W, hi.left y (hsub' y hy)]
      refine (prv_erase_of_ne ?_).symm
      intro he
      apply hyr
      rw [← nxt_prv' hA (hsub' y hy), he]
  · by_cases hyl : y = prv 0 B i.toNat
    · rw [W, hget, ite_eq_right (by omega), ite_eq_left (by rw [hyl])]
      rw [← W, hi.right _ hiI, hyl]
      exact (nxt_erase_prv hA hiB).symm
    · rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ← W, hi.right y (hsub' y hy)]
      refine (nxt_erase_of_ne ?_).symm
      intro he
      apply hyl
      rw [← prv_nxt' hA (hsub' y hy), he]

/-- Putting an item back right after removing it returns the array. -/
theorem relink_unlink {t : Array UInt64} {L : Layout} {B : Finset Nat} (hs : Static t L)
    (hsub : ∀ c ∈ B, 1 ≤ c ∧ c ≤ L.n) (hi : Items t L B) (hL : L.Good) {b i : UInt64}
    (hb : b.toNat = L.base) (hiB : i.toNat ∈ B) : relinkItem b i (unlinkItem b i t) = t := by
  have hA : Above 0 B := fun c hc => (hsub c hc).1
  have hget := unlink_get hs hsub hi hL hb hiB
  have hsize : t.size = L.base + 2 * (L.n + 1) := hs.size
  have hsmall := hL.small
  have hin := (hsub _ hiB).2
  have hi0 := (hsub _ hiB).1
  have hl : prv 0 B i.toNat ≤ L.n := by
    rcases prv_mem 0 B i.toNat with h | h
    · omega
    · exact (hsub _ h).2
  have hr : nxt 0 B i.toNat ≤ L.n := by
    rcases nxt_mem 0 B i.toNat with h | h
    · omega
    · exact (hsub _ h).2
  have hun := prv_ne hA hiB
  have hdn := nxt_ne hA hiB
  have hiI : i.toNat ∈ insert 0 B := mem_insert_of_mem hiB
  obtain ⟨e1, e2⟩ := idx_item b i (by omega)
  have r1 : (unlinkItem b i t)[L.base + 2 * i.toNat]! = t[L.base + 2 * i.toNat]! := by
    rw [hget, ite_eq_right (by omega), ite_eq_right (by omega)]
  have r2 : (unlinkItem b i t)[L.base + 2 * i.toNat + 1]! = t[L.base + 2 * i.toNat + 1]! := by
    rw [hget, ite_eq_right (by omega), ite_eq_right (by omega)]
  have wl := hi.left _ hiI
  have wr := hi.right _ hiI
  rw [W] at wl wr
  apply ext_get (by simp [relinkItem, unlinkItem])
  intro k hk
  simp only [relinkItem]
  rw [e1, e2, hb, r1, r2]
  obtain ⟨-, f2⟩ := idx_item b t[L.base + 2 * i.toNat]! (by omega)
  obtain ⟨f1, -⟩ := idx_item b t[L.base + 2 * i.toNat + 1]! (by omega)
  have hus : (unlinkItem b i t).size = t.size := by simp [unlinkItem]
  rw [f1, f2, hb, wl, wr, get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
    get_set _ _ _ _ (by omega)]
  split
  · rename_i hk1
    have := hi.left _ (nxt_mem_insert 0 B i.toNat)
    rw [prv_nxt hA hiB, W, ← hk1] at this
    exact (UInt64.toNat_inj.mp this).symm
  split
  · rename_i hk2 hk1
    have := hi.right _ (prv_mem_insert 0 B i.toNat)
    rw [nxt_prv hA hiB, W, ← hk1] at this
    exact (UInt64.toNat_inj.mp this).symm
  · rename_i hk2 hk1
    rw [hget, ite_eq_right hk1, ite_eq_right hk2]

/-- The item operations leave the words below `base`. -/
theorem unlink_below {t : Array UInt64} {L : Layout} {B : Finset Nat} (hs : Static t L)
    (hsub : ∀ c ∈ B, 1 ≤ c ∧ c ≤ L.n) (hi : Items t L B) (hL : L.Good) {b i : UInt64}
    (hb : b.toNat = L.base) (hiB : i.toNat ∈ B) :
    (unlinkItem b i t).size = t.size ∧ ∀ k < L.base, (unlinkItem b i t)[k]! = t[k]! := by
  refine ⟨by simp [unlinkItem], fun k hk => ?_⟩
  rw [unlink_get hs hsub hi hL hb hiB, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- `coverItem i` leaves the invariant of the other items, `uncoverItem i` undoes it, and the
column of `i` keeps its links. -/
theorem cover_inv {t : Array UInt64} {L : Layout} {B : Finset Nat} (hL : L.Good) (h : Inv t L B)
    {b i : UInt64} (hb : b.toNat = L.base) (hiB : i.toNat ∈ B) :
    Inv (coverItem b i t) L (B.erase i.toNat) ∧ uncoverItem b i (coverItem b i t) = t ∧
      Col (coverItem b i t) i.toNat (L.colQ (L.present B) i.toNat) := by
  set H := colOthers L (colList (L.colQ (L.present B) i.toNat))
  have hhide : hideColumn i t = delAll H t := hideColumn_eq hL h.static h.cols hiB
  obtain ⟨hs1, hc1, hQ1⟩ := colOthers_inv hL h.static h.cols (i := i.toNat)
    (colList (L.colQ (L.present B) i.toNat)).length
  rw [List.take_length] at hs1 hc1 hQ1
  obtain ⟨hnd, hq⟩ := colOthers_facts hL _ (colList_nodup _) fun r hr => mem_colList.mp hr
  have hi1 : Items (delAll H t) L B :=
    Items.delAll H t _ h.items h.cols hnd fun q hq' => ⟨(hq q hq').1, (hq q hq').2.1⟩
  obtain ⟨hsz2, hbelow⟩ := unlink_below hs1 h.sub hi1 hL hb hiB
  obtain ⟨hs2, hc2⟩ := below_base hs1 hc1 hsz2 hbelow
  have hcov : coverItem b i t = unlinkItem b i (delAll H t) := by rw [coverItem, hhide]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcov]
    refine ⟨hs2, fun c hc => h.sub c (mem_erase.mp hc).2,
      unlink_items hs1 h.sub hi1 hL hb hiB, ?_, fun c hc => ?_, fun c hc => ?_⟩
    · intro p hp
      exact (mem_filter.mp hp).2.1
    · exact h.cols.items c (mem_erase.mp hc).2
    · have := hc2.col c (mem_erase.mp hc).2
      rwa [colQ_cover (mem_erase.mp hc).1] at this
  · rw [hcov, uncoverItem, relink_unlink hs1 h.sub hi1 hL hb hiB]
    exact unhideColumn_eq hL h.static h.cols hiB
  · rw [hcov]
    have := hc2.col _ hiB
    rwa [hQ1] at this

end Library.Combinatorics.DancingLinks
