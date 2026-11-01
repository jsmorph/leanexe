import Library.Combinatorics.DancingLinks.Table
import Library.Combinatorics.DancingLinks.Program

/-! Knuth's `hide(p)` and `unhide(p)` in the program's array.  `Static t L` states the words that no
operation changes: the size of the array, the `TOP` of each option's node, and the `TOP`, `ULINK`,
and `DLINK` of each spacer.  `others L k m` lists the nodes that `hide` removes for node `p`,
position `m` of option `k`: the nodes after `p` up to the end of the option, and then the nodes from
the option's first node up to `p - 1`, since the spacer after the option leads back to its first
node.  `hide_eq` shows that `hide p t` is `delAll (others L k m) t`, and `unhide_eq` that `unhide p`
applied to that array returns `t`, since it walks the same nodes in the reverse order. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

namespace Layout

/-- The base of the item links, `3(Z + 1)`. -/
def base (L : Layout) : Nat := 3 * L.first L.os.length

/-- The options of a valid input: nonempty, without repeated items, and with items in `1..n`. -/
structure Good (L : Layout) : Prop where
  nonempty : ∀ k < L.os.length, 0 < L.len k
  nodup : ∀ k < L.os.length, (L.os[k]!).Nodup
  items : ∀ k < L.os.length, ∀ m < L.len k, 1 ≤ L.item k m ∧ L.item k m ≤ L.n
  small : L.base + 2 * (L.n + 1) < 2 ^ 60

/-- The nodes that `hide` removes for node `first k + m`, in its order. -/
def others (L : Layout) (k m : Nat) : List Nat :=
  List.range' (L.first k + m + 1) (L.len k - m - 1) ++ List.range' (L.first k) m

theorem first_succ (L : Layout) (k : Nat) : L.first (k + 1) = L.first k + L.len k + 1 := rfl

theorem first_le_last (L : Layout) {k : Nat} (hk : k < L.os.length) :
    L.first (k + 1) ≤ L.first L.os.length := L.first_le hk

/-- A spacer is no node of an option. -/
theorem spacer_not_node (L : Layout) {k : Nat} (hk : k ≤ L.os.length) :
    ¬ L.IsNode (L.first k - 1) := by
  rintro ⟨k', _, h1, h2⟩
  rcases Nat.lt_or_ge k' k with hlt | hge
  · have := L.first_le (Nat.succ_le_of_lt hlt)
    rw [first_succ] at this
    have := L.n_lt_first k
    omega
  · have := L.first_le hge
    have := L.n_lt_first k
    omega

theorem node_lt (L : Layout) {p : Nat} (hp : L.IsNode p) : L.n + 1 < p ∧ p < L.first L.os.length := by
  obtain ⟨k, hk, h1, h2⟩ := hp
  have := L.n_lt_first k
  have := L.first_le_last hk
  rw [first_succ] at this
  omega

end Layout

/-- The words that no operation of the search changes. -/
structure Static (t : Array UInt64) (L : Layout) : Prop where
  size : t.size = L.base + 2 * (L.n + 1)
  top : ∀ k < L.os.length, ∀ m < L.len k, W t (3 * (L.first k + m)) = L.item k m
  spacer : ∀ k ≤ L.os.length, W t (3 * (L.first k - 1)) = 0
  up : ∀ k < L.os.length, W t (3 * (L.first (k + 1) - 1) + 1) = L.first k
  down : ∀ k < L.os.length, W t (3 * (L.first k - 1) + 2) = L.first k + L.len k - 1

/-- The words that a removal writes belong to a header or to a node of an option. -/
theorem del_writes {t : Array UInt64} {L : Layout} {C P : Finset Nat} (h : Cols t L C P) {q : Nat}
    (hq : q ∈ P) (hc : L.nodeItem q ∈ C) (k : Nat)
    (hk : ∀ y, (y ≤ L.n ∨ L.IsNode y) → ∀ r < 3, (r = 0 → y ≤ L.n) → k ≠ 3 * y + r) :
    (del t q)[k]! = t[k]! := by
  set c := L.nodeItem q
  have hcol := h.col c hc
  have hqQ : q ∈ L.colQ P c := mem_filter.mpr ⟨hq, rfl⟩
  have hcn := h.items c hc
  have hins : ∀ y ∈ insert c (L.colQ P c), y ≤ L.n ∨ L.IsNode y := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact Or.inl hcn
    · exact Or.inr (h.nodes y (colQ_node hy).1)
  rw [del_get hcol hqQ,
    ite_eq_right (by have := hk c (Or.inl hcn) 0 (by omega) fun _ => hcn; omega),
    ite_eq_right (hk _ (hins _ (nxt_mem_insert _ _ _)) 1 (by omega) (by omega)),
    ite_eq_right (hk _ (hins _ (prv_mem_insert _ _ _)) 2 (by omega) (by omega))]

theorem Static.del {t : Array UInt64} {L : Layout} {C P : Finset Nat} (hs : Static t L)
    (h : Cols t L C P) {q : Nat} (hq : q ∈ P) (hc : L.nodeItem q ∈ C) : Static (del t q) L := by
  have hw := del_writes h hq hc
  have hnode : ∀ y, L.IsNode y → L.n + 1 < y := fun y hy => (L.node_lt hy).1
  refine ⟨by rw [del_size]; exact hs.size, ?_, ?_, ?_, ?_⟩
  · intro k hk m hm
    rw [W, hw]
    · exact hs.top k hk m hm
    · intro y hy r hr hr0
      have hat : L.IsNode (L.first k + m) := L.at_isNode ⟨hk, hm, rfl⟩
      have := hnode _ hat
      rcases hy with hy | hy <;> omega
  · intro k hk
    rw [W, hw]
    · exact hs.spacer k hk
    · intro y _ r hr hr0
      have := L.n_lt_first k
      omega
  · intro k hk
    rw [W, hw]
    · exact hs.up k hk
    · intro y hy r hr _
      have hsp := L.spacer_not_node (Nat.succ_le_of_lt hk)
      have := L.n_lt_first (k + 1)
      rcases hy with hy | hy
      · omega
      · intro he
        have : y = L.first (k + 1) - 1 := by omega
        exact hsp (this ▸ hy)
  · intro k hk
    rw [W, hw]
    · exact hs.down k hk
    · intro y hy r hr _
      have hsp := L.spacer_not_node (Nat.le_of_lt hk)
      have := L.n_lt_first k
      rcases hy with hy | hy
      · omega
      · intro he
        have : y = L.first k - 1 := by omega
        exact hsp (this ▸ hy)

theorem delAll_append (l l' : List Nat) (t : Array UInt64) :
    delAll (l ++ l') t = delAll l' (delAll l t) := by
  induction l generalizing t with
  | nil => rfl
  | cons q l ih => exact ih (del t q)

theorem rstAll_append (l l' : List Nat) (t : Array UInt64) :
    rstAll (l ++ l') t = rstAll l (rstAll l' t) := by
  induction l with
  | nil => rfl
  | cons q l ih => rw [List.cons_append, rstAll, rstAll, ih]

/-- Removals keep the static words and the columns. -/
theorem delAll_inv {L : Layout} {C : Finset Nat} :
    ∀ (l : List Nat) (t : Array UInt64) (P : Finset Nat), Static t L → Cols t L C P → l.Nodup →
      (∀ q ∈ l, q ∈ P ∧ L.nodeItem q ∈ C) →
      Static (delAll l t) L ∧ Cols (delAll l t) L C (P \ l.toFinset)
  | [], t, P, hs, h, _, _ => by simp [delAll, hs, h]
  | q :: l, t, P, hs, h, hnd, hl => by
    obtain ⟨hqP, hqC⟩ := hl q List.mem_cons_self
    have hl' : ∀ q' ∈ l, q' ∈ P.erase q ∧ L.nodeItem q' ∈ C := by
      intro q' hq'
      obtain ⟨h1, h2⟩ := hl q' (List.mem_cons_of_mem _ hq')
      refine ⟨mem_erase.mpr ⟨?_, h1⟩, h2⟩
      rintro rfl
      exact (List.nodup_cons.mp hnd).1 hq'
    obtain ⟨hs', hc'⟩ := delAll_inv l (del t q) (P.erase q) (hs.del h hqP hqC) (h.del hqP hqC)
      (List.nodup_cons.mp hnd).2 hl'
    have : P.erase q \ l.toFinset = P \ (q :: l).toFinset := by
      ext y; simp only [mem_sdiff, mem_erase, List.toFinset_cons, mem_insert, List.mem_toFinset]
      tauto
    rw [delAll]
    rw [this] at hc'
    exact ⟨hs', hc'⟩

theorem idx3 (q : UInt64) (h : 3 * q.toNat + 2 < 2 ^ 64) :
    (3 * q).toNat = 3 * q.toNat ∧ (3 * q + 1).toNat = 3 * q.toNat + 1 ∧
      (3 * q + 2).toNat = 3 * q.toNat + 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat] <;> omega

/-- A step of `hide` at a present node `q` of a tracked column is `del`. -/
theorem hide_step {t : Array UInt64} {L : Layout} {C P : Finset Nat} (h : Cols t L C P)
    (hsize : t.size < 2 ^ 60) {q : UInt64} (hq : q.toNat ∈ P) (hc : L.nodeItem q.toNat ∈ C) :
    ((t.set! (3 * t[(3 * q + 1).toNat]! + 2).toNat t[(3 * q + 2).toNat]!).set!
        (3 * t[(3 * q + 2).toNat]! + 1).toNat t[(3 * q + 1).toNat]!).set!
        (3 * t[(3 * q).toNat]!).toNat (t[(3 * t[(3 * q).toNat]!).toNat]! - 1) =
      del t q.toNat := by
  set c := L.nodeItem q.toNat
  have hcol := h.col c hc
  have hqQ : q.toNat ∈ L.colQ P c := mem_filter.mpr ⟨hq, rfl⟩
  have hqs := hcol.size _ (mem_insert_of_mem hqQ)
  obtain ⟨e0, e1, e2⟩ := idx3 q (by omega)
  have hu := hcol.size _ (prv_mem_insert c (L.colQ P c) q.toNat)
  have hd := hcol.size _ (nxt_mem_insert c (L.colQ P c) q.toNat)
  have hcs := hcol.size _ (mem_insert_self c (L.colQ P c))
  have wu : W t (3 * q.toNat + 1) = prv c (L.colQ P c) q.toNat := hcol.up _ (mem_insert_of_mem hqQ)
  have wd : W t (3 * q.toNat + 2) = nxt c (L.colQ P c) q.toNat :=
    hcol.down _ (mem_insert_of_mem hqQ)
  have wx : W t (3 * q.toNat) = c := hcol.top _ hqQ
  rw [e0, e1, e2]
  rw [W] at wu wd wx
  obtain ⟨f0, -, -⟩ := idx3 t[3 * q.toNat]! (by omega)
  obtain ⟨-, f1, -⟩ := idx3 t[3 * q.toNat + 2]! (by omega)
  obtain ⟨-, -, f2⟩ := idx3 t[3 * q.toNat + 1]! (by omega)
  rw [f0, f1, f2]
  rfl

/-- `hide p` removes the other nodes of `p`'s option, in the order of `others`. -/
theorem hide_eq {t : Array UInt64} {L : Layout} {C P : Finset Nat} (hL : L.Good) (hs : Static t L)
    (h : Cols t L C P) {p : UInt64} {k m : Nat} (hat : L.At p.toNat k m)
    (hoth : ∀ q ∈ L.others k m, q ∈ P ∧ L.nodeItem q ∈ C) :
    hide p t = delAll (L.others k m) t := by
  obtain ⟨hk, hm, hp⟩ := hat
  have hsize : t.size < 2 ^ 60 := by rw [hs.size]; exact hL.small
  have hlast := L.first_le_last hk
  rw [Layout.first_succ] at hlast
  have hbase : 3 * L.first L.os.length ≤ t.size := by rw [hs.size, Layout.base]; omega
  set a := L.len k - m - 1 with ha
  have hnd1 : ∀ j, (List.range' (p.toNat + 1) j).Nodup := fun j => List.nodup_range' ..
  have hoth' : ∀ l, l <+: L.others k m →
      Static (delAll l t) L ∧ Cols (delAll l t) L C (P \ l.toFinset) := by
    intro l hl
    have hnd : (L.others k m).Nodup := by
      unfold Layout.others
      refine List.nodup_append.mpr ⟨List.nodup_range' .., List.nodup_range' .., ?_⟩
      intro x hx y hy
      simp only [List.mem_range'_1] at hx hy
      omega
    exact delAll_inv l t P hs h (hnd.sublist hl.sublist) fun q hq => hoth q (hl.subset hq)
  let Inv : UInt64 × Array UInt64 → Prop := fun s =>
    (∃ j ≤ a, s.1.toNat = p.toNat + 1 + j ∧ s.2 = delAll (List.range' (p.toNat + 1) j) t) ∨
      (∃ j ≤ m, s.1.toNat = L.first k + j ∧
        s.2 = delAll (List.range' (p.toNat + 1) a ++ List.range' (L.first k) j) t)
  let μ : UInt64 × Array UInt64 → Nat := fun s =>
    if p.toNat < s.1.toNat then L.first k + L.len k - s.1.toNat + m + 1 else p.toNat - s.1.toNat
  have hpre1 : ∀ j ≤ a, List.range' (p.toNat + 1) j <+: L.others k m := by
    intro j hj
    unfold Layout.others
    rw [← hp]
    refine List.IsPrefix.trans ?_ (List.prefix_append _ _)
    have : List.range' (p.toNat + 1) a = List.range' (p.toNat + 1) j ++
        List.range' (p.toNat + 1 + j) (a - j) := by
      rw [List.range'_append_1]; congr 1; omega
    rw [this]
    exact List.prefix_append _ _
  have hpre2 : ∀ j ≤ m, List.range' (p.toNat + 1) a ++ List.range' (L.first k) j <+:
      L.others k m := by
    intro j hj
    unfold Layout.others
    rw [← hp]
    apply List.prefix_append_right_inj _ |>.mpr
    have : List.range' (L.first k) m = List.range' (L.first k) j ++
        List.range' (L.first k + j) (m - j) := by
      rw [List.range'_append_1]; congr 1; omega
    rw [this]
    exact List.prefix_append _ _
  have hfuel : μ (p + 1, t) < t.size.toUInt64.toNat := by
    have hp1 : (p + 1).toNat = p.toNat + 1 := by
      simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
    simp only [μ, hp1]
    rw [size_toUInt64 t (by omega)]
    split <;> omega
  have hinit : Inv (p + 1, t) := by
    left
    refine ⟨0, Nat.zero_le _, ?_, rfl⟩
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  unfold hide
  dsimp only
  refine repeatWhile_of_inv _ _ _ _ Inv μ (fun s => s.2 = delAll (L.others k m) t) hinit hfuel ?_ ?_
  rotate_left
  all_goals clear hinit hfuel
  · rintro ⟨q, t'⟩ hI hc
    simp only [Inv] at hI
    dsimp only at hI hc ⊢
    simp only [decide_eq_false_iff_not, not_not] at hc
    rcases hI with ⟨j, hj, hq, -⟩ | ⟨j, hj, hq, ht⟩
    · rw [hc] at hq; omega
    · rw [hc] at hq
      have hjm : j = m := by omega
      rw [ht, hjm]
      unfold Layout.others
      rw [← hp]
  · rintro ⟨q, t'⟩ hI hcond
    simp only [Inv] at hI ⊢
    dsimp only at hI hcond ⊢
    simp only [ne_eq, decide_eq_true_eq] at hcond
    have hqp : q.toNat ≠ p.toNat := fun e => hcond (UInt64.toNat_inj.mp e)
    rcases hI with ⟨j, hj, hq, ht⟩ | ⟨j, hj, hq, ht⟩
    · obtain ⟨hs', hc'⟩ := hoth' _ (hpre1 j hj)
      by_cases hja : j < a
      · -- A node of the option after `p`: remove it.
        have hat' : L.At q.toNat k (m + 1 + j) := ⟨hk, by omega, by omega⟩
        have hqP : q.toNat ∈ P \ (List.range' (p.toNat + 1) j).toFinset := by
          refine mem_sdiff.mpr ⟨(hoth _ ?_).1, ?_⟩
          · unfold Layout.others; rw [← hp]
            exact List.mem_append_left _ (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
          · simp only [List.mem_toFinset, List.mem_range'_1]; omega
        have hqC : L.nodeItem q.toNat ∈ C := by
          refine (hoth _ ?_).2
          unfold Layout.others; rw [← hp]
          exact List.mem_append_left _ (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
        have htop : W t' (3 * q.toNat) = L.item k (m + 1 + j) := by
          rw [ht, hq, show p.toNat + 1 + j = L.first k + (m + 1 + j) by omega]
          exact hs'.top k hk (m + 1 + j) (by omega)
        have hitem := (hL.items k hk (m + 1 + j) (by omega)).1
        obtain ⟨e0, -, -⟩ := idx3 q (by have := hs'.size; omega)
        have hx : t'[(3 * q).toNat]! ≠ 0 := by
          rw [e0]; intro h0; rw [W, h0] at htop; simp at htop; omega
        refine ⟨?_, ?_⟩
        · left
          refine ⟨j + 1, by omega, ?_, ?_⟩
          · simp only [ite_eq_right hx, UInt64.toNat_add, UInt64.reduceToNat]; omega
          · simp only [ite_eq_right hx]
            rw [ht]
            rw [hide_step hc' (by rw [delAll_size]; omega) hqP hqC, List.range'_concat,
              delAll_append, delAll, delAll, hq]
            congr 1; omega
        · simp only [μ]
          have hq1 : (q + 1).toNat = q.toNat + 1 := by
            simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
          simp only [ite_eq_right hx, hq1]
          rw [ite_eq_left (by omega), ite_eq_left (by omega)]
          omega
      · -- The spacer after the option: go back to its first node.
        have hja' : j = a := by omega
        have hsp : q.toNat = L.first (k + 1) - 1 := by rw [Layout.first_succ]; omega
        obtain ⟨e0, e1, -⟩ := idx3 q (by have := hs'.size; omega)
        have hx : t'[(3 * q).toNat]! = 0 := by
          have := hs'.spacer (k + 1) hk
          rw [e0, hsp]; rw [ht]
          exact UInt64.toNat_inj.mp (by rw [UInt64.toNat_zero]; exact this)
        have hup : (t'[(3 * q + 1).toNat]!).toNat = L.first k := by
          rw [e1, hsp, ht]; exact hs'.up k hk
        refine ⟨?_, ?_⟩
        · right
          refine ⟨0, Nat.zero_le _, ?_, ?_⟩
          · simp only [ite_eq_left hx]; rw [hup]; rfl
          · simp only [ite_eq_left hx]; rw [ht, hja', List.range'_zero, List.append_nil]
        · simp only [μ, ite_eq_left hx, hup]
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
          omega
    · obtain ⟨hs', hc'⟩ := hoth' _ (hpre2 j hj)
      have hjm : j < m := by
        rcases Nat.lt_or_ge j m with h' | h'
        · exact h'
        · exact absurd (by omega : q.toNat = p.toNat) hqp
      have hat' : L.At q.toNat k j := ⟨hk, by omega, by omega⟩
      have hmem : q.toNat ∈ L.others k m := by
        unfold Layout.others
        exact List.mem_append_right _ (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      have hqP : q.toNat ∈ P \ (List.range' (p.toNat + 1) a ++
          List.range' (L.first k) j).toFinset := by
        refine mem_sdiff.mpr ⟨(hoth _ hmem).1, ?_⟩
        simp only [List.mem_toFinset, List.mem_append, List.mem_range'_1, not_or]
        omega
      have hqC : L.nodeItem q.toNat ∈ C := (hoth _ hmem).2
      have htop : W t' (3 * q.toNat) = L.item k j := by
        rw [ht, hq]; exact hs'.top k hk j (by omega)
      have hitem := (hL.items k hk j (by omega)).1
      obtain ⟨e0, -, -⟩ := idx3 q (by have := hs'.size; omega)
      have hx : t'[(3 * q).toNat]! ≠ 0 := by
        rw [e0]; intro h0; rw [W, h0] at htop; simp at htop; omega
      refine ⟨?_, ?_⟩
      · right
        refine ⟨j + 1, by omega, ?_, ?_⟩
        · simp only [ite_eq_right hx, UInt64.toNat_add, UInt64.reduceToNat]; omega
        · simp only [ite_eq_right hx]
          rw [ht]
          rw [hide_step hc' (by rw [delAll_size]; omega) hqP hqC, List.range'_concat,
            ← List.append_assoc, delAll_append _ [_], delAll, delAll, hq, Nat.one_mul]
      · simp only [μ]
        have hq1 : (q + 1).toNat = q.toNat + 1 := by
          simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
        simp only [ite_eq_right hx, hq1]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        omega

/-- A step of `unhide` at a node `q` removed from a tracked column of `X` returns `X`. -/
theorem unhide_step {X : Array UInt64} {L : Layout} {C P : Finset Nat} (h : Cols X L C P)
    (hsize : X.size < 2 ^ 60) {q : UInt64} (hq : q.toNat ∈ P) (hc : L.nodeItem q.toNat ∈ C) :
    (((del X q.toNat).set! (3 * (del X q.toNat)[(3 * q + 1).toNat]! + 2).toNat q).set!
        (3 * (del X q.toNat)[(3 * q + 2).toNat]! + 1).toNat q).set!
        (3 * (del X q.toNat)[(3 * q).toNat]!).toNat
        ((del X q.toNat)[(3 * (del X q.toNat)[(3 * q).toNat]!).toNat]! + 1) = X := by
  set c := L.nodeItem q.toNat
  have hcol := h.col c hc
  have hqQ : q.toNat ∈ L.colQ P c := mem_filter.mpr ⟨hq, rfl⟩
  have hA := hcol.above
  have hqs := hcol.size _ (mem_insert_of_mem hqQ)
  obtain ⟨e0, e1, e2⟩ := idx3 q (by omega)
  have hu := hcol.size _ (prv_mem_insert c (L.colQ P c) q.toNat)
  have hd := hcol.size _ (nxt_mem_insert c (L.colQ P c) q.toNat)
  have hun := prv_ne hA hqQ
  have hdn := nxt_ne hA hqQ
  have hqc : c < q.toNat := hA _ hqQ
  have hget := del_get hcol hqQ
  have r0 : (del X q.toNat)[3 * q.toNat]! = X[3 * q.toNat]! := by
    rw [hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  have r1 : (del X q.toNat)[3 * q.toNat + 1]! = X[3 * q.toNat + 1]! := by
    rw [hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  have r2 : (del X q.toNat)[3 * q.toNat + 2]! = X[3 * q.toNat + 2]! := by
    rw [hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  have wu : W X (3 * q.toNat + 1) = prv c (L.colQ P c) q.toNat := hcol.up _ (mem_insert_of_mem hqQ)
  have wd : W X (3 * q.toNat + 2) = nxt c (L.colQ P c) q.toNat :=
    hcol.down _ (mem_insert_of_mem hqQ)
  have wx : W X (3 * q.toNat) = c := hcol.top _ hqQ
  rw [e0, e1, e2, r0, r1, r2]
  rw [W] at wu wd wx
  obtain ⟨f0, -, -⟩ := idx3 X[3 * q.toNat]! (by omega)
  obtain ⟨-, f1, -⟩ := idx3 X[3 * q.toNat + 2]! (by omega)
  obtain ⟨-, -, f2⟩ := idx3 X[3 * q.toNat + 1]! (by omega)
  rw [f0, f1, f2]
  refine Eq.trans ?_ (rst_del hcol hqQ)
  simp only [rst, W, r0, r1, r2, UInt64.ofNat_toNat]

/-- `unhide p`, applied to the array that `hide p` leaves, returns the array before `hide`. -/
theorem unhide_eq {t : Array UInt64} {L : Layout} {C P : Finset Nat} (hL : L.Good) (hs : Static t L)
    (h : Cols t L C P) {p : UInt64} {k m : Nat} (hat : L.At p.toNat k m)
    (hoth : ∀ q ∈ L.others k m, q ∈ P ∧ L.nodeItem q ∈ C) :
    unhide p (delAll (L.others k m) t) = t := by
  obtain ⟨hk, hm, hp⟩ := hat
  have hsize : t.size < 2 ^ 60 := by rw [hs.size]; exact hL.small
  have hlast := L.first_le_last hk
  rw [Layout.first_succ] at hlast
  have hbase : 3 * L.first L.os.length ≤ t.size := by rw [hs.size, Layout.base]; omega
  have hn1 := L.n_lt_first k
  set a := L.len k - m - 1 with ha
  have hnd : (L.others k m).Nodup := by
    unfold Layout.others
    refine List.nodup_append.mpr ⟨List.nodup_range' .., List.nodup_range' .., ?_⟩
    intro x hx y hy
    simp only [List.mem_range'_1] at hx hy
    omega
  have hpre : ∀ l, l <+: L.others k m →
      Static (delAll l t) L ∧ Cols (delAll l t) L C (P \ l.toFinset) := fun l hl =>
    delAll_inv l t P hs h (hnd.sublist hl.sublist) fun q hq => hoth q (hl.subset hq)
  have hpre1 : ∀ j ≤ a, List.range' (p.toNat + 1) j <+: L.others k m := by
    intro j hj
    unfold Layout.others
    rw [← hp]
    refine List.IsPrefix.trans ?_ (List.prefix_append _ _)
    have : List.range' (p.toNat + 1) a = List.range' (p.toNat + 1) j ++
        List.range' (p.toNat + 1 + j) (a - j) := by
      rw [List.range'_append_1]; congr 1; omega
    rw [this]
    exact List.prefix_append _ _
  have hpre2 : ∀ j ≤ m, List.range' (p.toNat + 1) a ++ List.range' (L.first k) j <+:
      L.others k m := by
    intro j hj
    unfold Layout.others
    rw [← hp]
    apply List.prefix_append_right_inj _ |>.mpr
    have : List.range' (L.first k) m = List.range' (L.first k) j ++
        List.range' (L.first k + j) (m - j) := by
      rw [List.range'_append_1]; congr 1; omega
    rw [this]
    exact List.prefix_append _ _
  have hoth_mem : ∀ q ∈ L.others k m, q ∈ P ∧ L.nodeItem q ∈ C := hoth
  let Inv : UInt64 × Array UInt64 → Prop := fun s =>
    (∃ i ≤ m, s.1.toNat + 1 = L.first k + i ∧
      s.2 = delAll (List.range' (p.toNat + 1) a ++ List.range' (L.first k) i) t) ∨
      (∃ i ≤ a, s.1.toNat = p.toNat + i ∧ s.2 = delAll (List.range' (p.toNat + 1) i) t)
  let μ : UInt64 × Array UInt64 → Nat := fun s =>
    if s.1.toNat < p.toNat then s.1.toNat + 1 - L.first k + a + 1 else s.1.toNat - p.toNat
  have hp1 : (p - 1).toNat = p.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  have hfuel : μ (p - 1, delAll (L.others k m) t) <
      (delAll (L.others k m) t).size.toUInt64.toNat := by
    have e : μ (p - 1, delAll (L.others k m) t) = (p - 1).toNat + 1 - L.first k + a + 1 := by
      show (if (p - 1).toNat < p.toNat then (p - 1).toNat + 1 - L.first k + a + 1
        else (p - 1).toNat - p.toNat) = _
      rw [ite_eq_left (by rw [hp1]; omega)]
    rw [e, hp1, delAll_size, size_toUInt64 t (by omega)]
    omega
  have hinit : Inv (p - 1, delAll (L.others k m) t) := by
    left
    refine ⟨m, le_rfl, ?_, ?_⟩
    · show (p - 1).toNat + 1 = L.first k + m
      rw [hp1]; omega
    · unfold Layout.others; rw [← hp]
  unfold unhide
  dsimp only
  refine repeatWhile_of_inv _ _ _ _ Inv μ (fun s => s.2 = t) hinit hfuel ?_ ?_
  rotate_left
  all_goals clear hinit hfuel
  · rintro ⟨q, t'⟩ hI hc
    simp only [Inv] at hI
    dsimp only at hI hc ⊢
    simp only [decide_eq_false_iff_not, not_not] at hc
    rcases hI with ⟨i, hi, hq, -⟩ | ⟨i, hi, hq, ht⟩
    · rw [hc] at hq; omega
    · rw [hc] at hq
      have hi0 : i = 0 := by omega
      rw [ht, hi0]; rfl
  · rintro ⟨q, t'⟩ hI hcond
    simp only [Inv] at hI ⊢
    dsimp only at hI hcond ⊢
    simp only [ne_eq, decide_eq_true_eq] at hcond
    have hqp : q.toNat ≠ p.toNat := fun e => hcond (UInt64.toNat_inj.mp e)
    rcases hI with ⟨i, hi, hq, ht⟩ | ⟨i, hi, hq, ht⟩
    · by_cases hi0 : i = 0
      · -- The spacer before the option: go forward to its last node.
        have hsp : q.toNat = L.first k - 1 := by omega
        obtain ⟨hs', -⟩ := hpre _ (hpre2 0 (Nat.zero_le _))
        rw [hi0] at ht
        obtain ⟨e0, -, e2⟩ := idx3 q (by have := hs'.size; omega)
        have hx : t'[(3 * q).toNat]! = 0 := by
          have := hs'.spacer k (Nat.le_of_lt hk)
          rw [e0, hsp, ht]
          exact UInt64.toNat_inj.mp (by rw [UInt64.toNat_zero]; exact this)
        have hdn : (t'[(3 * q + 2).toNat]!).toNat = L.first k + L.len k - 1 := by
          rw [e2, hsp, ht]; exact hs'.down k hk
        refine ⟨?_, ?_⟩
        · right
          refine ⟨a, le_rfl, ?_, ?_⟩
          · simp only [ite_eq_left hx]; rw [hdn]; omega
          · simp only [ite_eq_left hx]; rw [ht, List.range'_zero, List.append_nil]
        · simp only [μ, ite_eq_left hx, hdn]
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
          omega
      · -- A node of the option before `p`: restore it.
        have hqn : q.toNat = L.first k + (i - 1) := by omega
        have hsplit : List.range' (p.toNat + 1) a ++ List.range' (L.first k) i =
            (List.range' (p.toNat + 1) a ++ List.range' (L.first k) (i - 1)) ++ [q.toNat] := by
          rw [List.append_assoc, hqn, ← List.range'_1_concat]
          congr 2; omega
        obtain ⟨hs', hc'⟩ := hpre _ (hpre2 (i - 1) (by omega))
        have hmem : q.toNat ∈ L.others k m := by
          unfold Layout.others
          exact List.mem_append_right _ (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
        have hqP : q.toNat ∈ P \ (List.range' (p.toNat + 1) a ++
            List.range' (L.first k) (i - 1)).toFinset := by
          refine mem_sdiff.mpr ⟨(hoth _ hmem).1, ?_⟩
          simp only [List.mem_toFinset, List.mem_append, List.mem_range'_1, not_or]
          omega
        have hqC : L.nodeItem q.toNat ∈ C := (hoth _ hmem).2
        have htop : W t' (3 * q.toNat) = L.item k (i - 1) := by
          rw [ht, hsplit, delAll_append, delAll, delAll, W]
          have hX := hc'.col _ hqC
          have hqQ : q.toNat ∈ L.colQ _ (L.nodeItem q.toNat) := mem_filter.mpr ⟨hqP, rfl⟩
          rw [del_get hX hqQ, ite_eq_right (by have := hX.above _ hqQ; omega),
            ite_eq_right (by have := nxt_ne hX.above hqQ; omega),
            ite_eq_right (by have := prv_ne hX.above hqQ; omega), ← W, hqn]
          exact hs'.top k hk (i - 1) (by omega)
        have hitem := (hL.items k hk (i - 1) (by omega)).1
        obtain ⟨e0, -, -⟩ := idx3 q (by have := hs'.size; omega)
        have hx : t'[(3 * q).toNat]! ≠ 0 := by
          rw [e0]; intro h0; rw [W, h0] at htop; simp at htop; omega
        have hq1 : (q - 1).toNat = q.toNat - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
        refine ⟨?_, ?_⟩
        · left
          refine ⟨i - 1, by omega, by simp only [ite_eq_right hx, hq1]; omega, ?_⟩
          simp only [ite_eq_right hx]
          rw [ht, hsplit, delAll_append, delAll, delAll]
          exact unhide_step hc' (by rw [delAll_size]; omega) hqP hqC
        · simp only [μ, ite_eq_right hx, hq1]
          rw [ite_eq_left (by omega), ite_eq_left (by omega)]
          omega
    · -- A node of the option after `p`: restore it.
      have hi0 : i ≠ 0 := fun e => hqp (by omega)
      have hsplit : List.range' (p.toNat + 1) i =
          List.range' (p.toNat + 1) (i - 1) ++ [q.toNat] := by
        rw [show q.toNat = p.toNat + 1 + (i - 1) by omega, ← List.range'_1_concat]
        congr 1; omega
      obtain ⟨hs', hc'⟩ := hpre _ (hpre1 (i - 1) (by omega))
      have hmem : q.toNat ∈ L.others k m := by
        unfold Layout.others; rw [← hp]
        exact List.mem_append_left _ (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      have hqP : q.toNat ∈ P \ (List.range' (p.toNat + 1) (i - 1)).toFinset := by
        refine mem_sdiff.mpr ⟨(hoth _ hmem).1, ?_⟩
        simp only [List.mem_toFinset, List.mem_range'_1]; omega
      have hqC : L.nodeItem q.toNat ∈ C := (hoth _ hmem).2
      have htop : W t' (3 * q.toNat) = L.item k (m + i) := by
        rw [ht, hsplit, delAll_append, delAll, delAll, W]
        have hX := hc'.col _ hqC
        have hqQ : q.toNat ∈ L.colQ _ (L.nodeItem q.toNat) := mem_filter.mpr ⟨hqP, rfl⟩
        rw [del_get hX hqQ, ite_eq_right (by have := hX.above _ hqQ; omega),
          ite_eq_right (by have := nxt_ne hX.above hqQ; omega),
          ite_eq_right (by have := prv_ne hX.above hqQ; omega), ← W,
          show q.toNat = L.first k + (m + i) by omega]
        exact hs'.top k hk (m + i) (by omega)
      have hitem := (hL.items k hk (m + i) (by omega)).1
      obtain ⟨e0, -, -⟩ := idx3 q (by have := hs'.size; omega)
      have hx : t'[(3 * q).toNat]! ≠ 0 := by
        rw [e0]; intro h0; rw [W, h0] at htop; simp at htop; omega
      have hq1 : (q - 1).toNat = q.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      refine ⟨?_, ?_⟩
      · right
        refine ⟨i - 1, by omega, by simp only [ite_eq_right hx, hq1]; omega, ?_⟩
        simp only [ite_eq_right hx]
        rw [ht, hsplit, delAll_append, delAll, delAll]
        exact unhide_step hc' (by rw [delAll_size]; omega) hqP hqC
      · simp only [μ, ite_eq_right hx, hq1]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        omega

end Library.Combinatorics.DancingLinks
