import Library.Combinatorics.DancingLinks.Table
import Library.Combinatorics.DancingLinks.Program

/-! Knuth's `hide(p)` and `unhide(p)` in the program's array.  `Static t L` states the words that no
operation changes: the size of the array, the `TOP` of each option's node, and the `TOP`, `ULINK`,
and `DLINK` of each spacer.  `others L k m` lists the nodes that `hide` removes for node `p`,
position `m` of option `k`: the nodes after `p` up to the end of the option, and then the nodes from
the option's first node up to `p - 1`, since the spacer after the option leads back to its first
node.  `hide_eq` shows that `hide p t` is `delAll (others L k m) t`, and `unhide_eq` that `unhide p`
applied to that array returns `t`, since it walks the same nodes in the reverse order.  This file
proves the steps, `hide_step` and `unhide_step`, and the walks that compose them are in
`Walk.lean`. -/

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

theorem others_nodup (L : Layout) (k m : Nat) : (L.others k m).Nodup := by
  unfold others
  refine List.nodup_append.mpr ⟨List.nodup_range' .., List.nodup_range' .., ?_⟩
  intro x hx y hy
  simp only [List.mem_range'_1] at hx hy
  omega

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

end Library.Combinatorics.DancingLinks
