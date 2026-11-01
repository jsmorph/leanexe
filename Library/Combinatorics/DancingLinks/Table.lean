import Library.Combinatorics.DancingLinks.Delete
import Library.Combinatorics.DancingLinks.Count

/-! The layout of the nodes and the columns of all items.  A `Layout` holds the number of items and
the options.  Node `first k` is the first node of option `k`, the option's nodes follow, and a
spacer follows each option, so `first (k + 1) = first k + len k + 1`, node `first 0 - 1 = N + 1`
is the first spacer, and node `first M - 1` is the last.  `At p k m` states that node `p` is
position `m` of option `k`.  `Cols t L C P` states that each tracked item `c ∈ C` has its column
in `t` with the present nodes of `P` whose item is `c`.  `delAll` removes the nodes of a list in
order, and `rstAll` restores them in the reverse order, and `rstAll_delAll` shows that the second
undoes the first for distinct present nodes of tracked columns, the order in which Knuth's
`uncover` reverses `cover`. -/

namespace Library.Combinatorics.DancingLinks

open Finset

/-- The number of items and the options of an input. -/
structure Layout where
  n : Nat
  os : List (List Nat)

namespace Layout

/-- The length of option `k`. -/
def len (L : Layout) (k : Nat) : Nat := (L.os[k]!).length

/-- Item `m` of option `k`. -/
def item (L : Layout) (k m : Nat) : Nat := (L.os[k]!)[m]!

/-- The first node of option `k`. -/
def first (L : Layout) : Nat → Nat
  | 0 => L.n + 2
  | k + 1 => L.first k + L.len k + 1

/-- Node `p` is position `m` of option `k`. -/
def At (L : Layout) (p k m : Nat) : Prop := k < L.os.length ∧ m < L.len k ∧ p = L.first k + m

/-- The option of a node, the first option whose nodes contain it. -/
def optOf (L : Layout) (p : Nat) : Nat :=
  ((List.range L.os.length).filter fun k => L.first k ≤ p ∧ p < L.first k + L.len k).headD 0

/-- Node `p` belongs to an option. -/
def IsNode (L : Layout) (p : Nat) : Prop :=
  ∃ k < L.os.length, L.first k ≤ p ∧ p < L.first k + L.len k

instance (L : Layout) : DecidablePred L.IsNode := fun p => by unfold IsNode; infer_instance

/-- The item of a node. -/
def nodeItem (L : Layout) (p : Nat) : Nat := L.item (L.optOf p) (p - L.first (L.optOf p))

/-- The nodes whose options lie inside `B`. -/
def present (L : Layout) (B : Finset Nat) : Finset Nat :=
  (range (L.first L.os.length)).filter fun p => L.IsNode p ∧ Inside L.os B (L.optOf p)

/-- The present nodes of `P` in the column of item `c`. -/
def colQ (L : Layout) (P : Finset Nat) (c : Nat) : Finset Nat := P.filter (L.nodeItem · = c)

theorem first_le (L : Layout) : ∀ {k k' : Nat}, k ≤ k' → L.first k ≤ L.first k' := by
  intro k k' h
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (by rw [first]; omega)

theorem first_lt (L : Layout) {k k' : Nat} (h : k < k') : L.first k + L.len k < L.first k' := by
  have := L.first_le (Nat.succ_le_of_lt h)
  rw [first] at this
  omega

theorem n_lt_first (L : Layout) (k : Nat) : L.n + 1 < L.first k := by
  have := L.first_le (Nat.zero_le k)
  rw [first] at this
  omega

theorem at_unique {L : Layout} {p k m k' m' : Nat} (h : L.At p k m) (h' : L.At p k' m') :
    k = k' ∧ m = m' := by
  obtain ⟨_, hm, hp⟩ := h
  obtain ⟨_, hm', hp'⟩ := h'
  rcases Nat.lt_trichotomy k k' with hlt | rfl | hlt
  · have := L.first_lt hlt; omega
  · omega
  · have := L.first_lt hlt; omega

theorem optOf_at {L : Layout} {p k m : Nat} (h : L.At p k m) : L.optOf p = k := by
  obtain ⟨hk, hm, hp⟩ := h
  unfold optOf
  set fil := (List.range L.os.length).filter (fun k => decide (L.first k ≤ p ∧
    p < L.first k + L.len k))
  have hmem : k ∈ fil := List.mem_filter.mpr ⟨List.mem_range.mpr hk, by simp; omega⟩
  have hall : ∀ k' ∈ fil, k' = k := by
    intro k' hk'
    obtain ⟨hk'r, hk'p⟩ := List.mem_filter.mp hk'
    simp only [decide_eq_true_eq] at hk'p
    have hat' : L.At p k' (p - L.first k') := ⟨List.mem_range.mp hk'r, by omega, by omega⟩
    exact (at_unique hat' ⟨hk, hm, hp⟩).1
  cases hf : fil with
  | nil => rw [hf] at hmem; simp at hmem
  | cons a t =>
    rw [List.headD_cons]
    exact hall a (by rw [hf]; exact List.mem_cons_self)

theorem nodeItem_at {L : Layout} {p k m : Nat} (h : L.At p k m) : L.nodeItem p = L.item k m := by
  unfold nodeItem
  rw [optOf_at h, h.2.2]
  congr 1
  omega

theorem isNode_iff (L : Layout) (p : Nat) :
    L.IsNode p ↔ L.At p (L.optOf p) (p - L.first (L.optOf p)) := by
  constructor
  · rintro ⟨k, hk, h1, h2⟩
    have hat : L.At p k (p - L.first k) := ⟨hk, by omega, by omega⟩
    rw [optOf_at hat]
    exact hat
  · intro h
    exact ⟨_, h.1, by have := h.2.2; omega, by have := h.2.1; have := h.2.2; omega⟩

theorem at_isNode {L : Layout} {p k m : Nat} (h : L.At p k m) : L.IsNode p :=
  ⟨k, h.1, by rw [h.2.2]; omega, by rw [h.2.2]; exact Nat.add_lt_add_left h.2.1 _⟩

theorem mem_present {L : Layout} {B : Finset Nat} {p k m : Nat} (h : L.At p k m) :
    p ∈ L.present B ↔ Inside L.os B k := by
  unfold present
  rw [mem_filter, optOf_at h]
  constructor
  · exact fun h' => h'.2.2
  · intro hin
    refine ⟨mem_range.mpr ?_, at_isNode h, hin⟩
    have := L.first_lt h.1
    have := h.2.1
    rw [h.2.2]
    by_cases hk : k + 1 < L.os.length
    · have := L.first_lt hk; rw [first] at *; omega
    · have : k + 1 = L.os.length := by have := h.1; omega
      rw [← this, first]; omega

end Layout

/-- The columns of the tracked items `C` hold the present nodes `P`. -/
structure Cols (t : Array UInt64) (L : Layout) (C P : Finset Nat) : Prop where
  nodes : ∀ p ∈ P, L.IsNode p
  items : ∀ c ∈ C, c ≤ L.n
  col : ∀ c ∈ C, Col t c (L.colQ P c)

/-- Removes the nodes of `l` in order. -/
def delAll : List Nat → Array UInt64 → Array UInt64
  | [], t => t
  | q :: l, t => delAll l (del t q)

/-- Restores the nodes of `l` in the reverse order. -/
def rstAll : List Nat → Array UInt64 → Array UInt64
  | [], t => t
  | q :: l, t => rst (rstAll l t) q

theorem delAll_size : ∀ (l : List Nat) (t : Array UInt64), (delAll l t).size = t.size
  | [], _ => rfl
  | q :: l, t => by rw [delAll, delAll_size l, del_size]

/-- The words of a header's column belong to the header and to nodes of the column. -/
theorem colQ_node {L : Layout} {P : Finset Nat} {c y : Nat} (h : y ∈ L.colQ P c) :
    y ∈ P ∧ L.nodeItem y = c := mem_filter.mp h

/-- Removing a present node of a tracked column keeps every tracked column, with the node gone. -/
theorem Cols.del {t : Array UInt64} {L : Layout} {C P : Finset Nat} (h : Cols t L C P) {q : Nat}
    (hq : q ∈ P) (hc : L.nodeItem q ∈ C) : Cols (del t q) L C (P.erase q) := by
  set c := L.nodeItem q
  have hcol := h.col c hc
  have hqQ : q ∈ L.colQ P c := mem_filter.mpr ⟨hq, rfl⟩
  have herase : L.colQ (P.erase q) c = (L.colQ P c).erase q := by
    ext y; simp only [Layout.colQ, mem_filter, mem_erase]; tauto
  refine ⟨fun p hp => h.nodes p (mem_erase.mp hp).2, h.items, fun c' hc' => ?_⟩
  by_cases hcc : c' = c
  · rw [hcc, herase]
    exact del_col hcol hqQ
  · have herase' : L.colQ (P.erase q) c' = L.colQ P c' := by
      ext y
      simp only [Layout.colQ, mem_filter, mem_erase]
      constructor
      · exact fun h => ⟨h.1.2, h.2⟩
      · intro h'
        refine ⟨⟨?_, h'.1⟩, h'.2⟩
        rintro rfl
        exact hcc (h'.2.symm.trans rfl)
    rw [herase']
    refine (h.col c' hc').frame (del_size t q) ?_
    intro y hy r hr
    rw [del_get hcol hqQ]
    have hc'n := h.items c' hc'
    have hcn := h.items c hc
    -- The words of column `c'` lie at its header and at nodes whose item is `c'`.
    have hyc : y ≠ c := by
      rcases mem_insert.mp hy with rfl | hy
      · exact hcc
      · have := L.n_lt_first 0
        have hn := (L.isNode_iff y).mp (h.nodes y (colQ_node hy).1)
        have := L.first_le (Nat.zero_le (L.optOf y))
        have := hn.2.2
        omega
    have hyd : ∀ w ∈ insert c (L.colQ P c), y ≠ w := by
      intro w hw
      rcases mem_insert.mp hw with rfl | hw
      · exact hyc
      · rintro rfl
        rcases mem_insert.mp hy with rfl | hy
        · have hn := (L.isNode_iff y).mp (h.nodes y (colQ_node hw).1)
          have := L.n_lt_first (L.optOf y)
          have := hn.2.2
          omega
        · exact hcc ((colQ_node hy).2.symm.trans (colQ_node hw).2)
    have h1 := hyd _ (nxt_mem_insert c (L.colQ P c) q)
    have h2 := hyd _ (prv_mem_insert c (L.colQ P c) q)
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Removing distinct present nodes of tracked columns in order, and then restoring them in the
reverse order, returns the array, and the removals keep the columns without the nodes. -/
theorem rstAll_delAll {L : Layout} {C : Finset Nat} :
    ∀ (l : List Nat) (t : Array UInt64) (P : Finset Nat), Cols t L C P → l.Nodup →
      (∀ q ∈ l, q ∈ P ∧ L.nodeItem q ∈ C) →
      Cols (delAll l t) L C (P \ l.toFinset) ∧ rstAll l (delAll l t) = t
  | [], t, P, h, _, _ => by simp [delAll, rstAll, h]
  | q :: l, t, P, h, hnd, hl => by
    obtain ⟨hqP, hqC⟩ := hl q List.mem_cons_self
    have h' := h.del hqP hqC
    have hl' : ∀ q' ∈ l, q' ∈ P.erase q ∧ L.nodeItem q' ∈ C := by
      intro q' hq'
      obtain ⟨h1, h2⟩ := hl q' (List.mem_cons_of_mem _ hq')
      refine ⟨mem_erase.mpr ⟨?_, h1⟩, h2⟩
      rintro rfl
      exact (List.nodup_cons.mp hnd).1 hq'
    obtain ⟨hcols, hrst⟩ := rstAll_delAll l (del t q) (P.erase q) h' (List.nodup_cons.mp hnd).2 hl'
    refine ⟨?_, ?_⟩
    · have : P.erase q \ l.toFinset = P \ (q :: l).toFinset := by
        ext y; simp only [mem_sdiff, mem_erase, List.toFinset_cons, mem_insert, List.mem_toFinset]
        tauto
      rw [delAll, ← this]
      exact hcols
    · rw [delAll, rstAll, hrst]
      have hqQ : q ∈ L.colQ P (L.nodeItem q) := mem_filter.mpr ⟨hqP, rfl⟩
      exact rst_del (h.col _ hqC) hqQ

end Library.Combinatorics.DancingLinks
