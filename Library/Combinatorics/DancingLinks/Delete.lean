import Library.Combinatorics.DancingLinks.Links
import LeanExe.Dialect.ArrayLemmas

/-! Removing and restoring a node of a column in the array.  Node `p` holds `TOP`, `ULINK`, and
`DLINK` in the words `3p`, `3p + 1`, and `3p + 2`, and a header keeps `LEN` in `TOP`.  `Col t c Q`
states that the words of header `c` and of the nodes `Q` form the column: each word `DLINK(y)` is
`nxt c Q y`, each `ULINK(y)` is `prv c Q y`, `LEN(c)` is the number of nodes, and each node's
`TOP` is `c`.  `del t q` performs the writes of Knuth's `hide` for node `q`, and `rst t q` those
of `unhide`.  `del_col` shows that removing a present node leaves the column of the other nodes,
`rst_del` that restoring it right after returns the array, and `Col.frame` that an array that
agrees on a column's words keeps the column. -/

namespace Library.Combinatorics.DancingLinks

open Finset LeanExe.Dialect

/-- Word `k` of `t` as a natural number. -/
def W (t : Array UInt64) (k : Nat) : Nat := (t[k]!).toNat

/-- The column of header `c` with present nodes `Q`. -/
structure Col (t : Array UInt64) (c : Nat) (Q : Finset Nat) : Prop where
  above : Above c Q
  size : ∀ y ∈ insert c Q, 3 * y + 2 < t.size
  len : W t (3 * c) = Q.card
  top : ∀ q ∈ Q, W t (3 * q) = c
  down : ∀ y ∈ insert c Q, W t (3 * y + 2) = nxt c Q y
  up : ∀ y ∈ insert c Q, W t (3 * y + 1) = prv c Q y

/-- The writes of `hide` that remove node `q` from its item's list. -/
def del (t : Array UInt64) (q : Nat) : Array UInt64 :=
  let x := W t (3 * q)
  ((t.set! (3 * W t (3 * q + 1) + 2) t[3 * q + 2]!).set! (3 * W t (3 * q + 2) + 1)
    t[3 * q + 1]!).set! (3 * x) (t[3 * x]! - 1)

/-- The writes of `unhide` that put node `q` back into its item's list. -/
def rst (t : Array UInt64) (q : Nat) : Array UInt64 :=
  let x := W t (3 * q)
  ((t.set! (3 * W t (3 * q + 1) + 2) (UInt64.ofNat q)).set! (3 * W t (3 * q + 2) + 1)
    (UInt64.ofNat q)).set! (3 * x) (t[3 * x]! + 1)

theorem nxt_mem_insert (c : Nat) (Q : Finset Nat) (y : Nat) : nxt c Q y ∈ insert c Q := by
  rcases nxt_mem c Q y with h | h
  · rw [h]; exact mem_insert_self c Q
  · exact mem_insert_of_mem h

theorem prv_mem_insert (c : Nat) (Q : Finset Nat) (y : Nat) : prv c Q y ∈ insert c Q := by
  rcases prv_mem c Q y with h | h
  · rw [h]; exact mem_insert_self c Q
  · exact mem_insert_of_mem h

/-- The predecessor of the header's successor is the header. -/
theorem prv_nxt_head {c : Nat} {Q : Finset Nat} (hA : Above c Q) : prv c Q (nxt c Q c) = c := by
  rcases nxt_mem c Q c with h | h
  · rw [h]
    unfold prv
    rw [ite_eq_left rfl]
    split
    · rename_i hne
      exfalso
      have hm := min'_mem Q hne
      unfold nxt at h
      have hne' : (Q.filter (c < ·)).Nonempty := ⟨_, mem_filter.mpr ⟨hm, hA _ hm⟩⟩
      rw [dite_eq_left hne'] at h
      have := (mem_filter.mp (min'_mem _ hne')).2
      omega
    · rfl
  · have hnc : nxt c Q c ≠ c := Nat.ne_of_gt (hA _ h)
    unfold prv
    rw [ite_eq_right hnc]
    split
    · rename_i hne
      exfalso
      obtain ⟨y, hy⟩ := hne
      obtain ⟨hyQ, hyl⟩ := mem_filter.mp hy
      unfold nxt at hyl
      have hne' : (Q.filter (c < ·)).Nonempty := ⟨y, mem_filter.mpr ⟨hyQ, hA y hyQ⟩⟩
      rw [dite_eq_left hne'] at hyl
      exact absurd hyl (not_lt.mpr (min'_le _ y (mem_filter.mpr ⟨hyQ, hA y hyQ⟩)))
    · rfl

/-- The successor of the header's predecessor is the header. -/
theorem nxt_prv_head (c : Nat) (Q : Finset Nat) : nxt c Q (prv c Q c) = c := by
  unfold prv
  rw [ite_eq_left rfl]
  split
  · rename_i hne
    unfold nxt
    have : ¬ (Q.filter (Q.max' hne < ·)).Nonempty := by
      rintro ⟨y, hy⟩
      obtain ⟨hyQ, hlt⟩ := mem_filter.mp hy
      have := le_max' Q y hyQ
      omega
    rw [dite_eq_right this]
  · unfold nxt
    have : ¬ (Q.filter (c < ·)).Nonempty := by
      rintro ⟨y, hy⟩
      rename_i hne
      exact hne ⟨y, (mem_filter.mp hy).1⟩
    rw [dite_eq_right this]

theorem prv_nxt' {c : Nat} {Q : Finset Nat} (hA : Above c Q) {y : Nat} (hy : y ∈ insert c Q) :
    prv c Q (nxt c Q y) = y := by
  rcases mem_insert.mp hy with rfl | hy
  · exact prv_nxt_head hA
  · exact prv_nxt hA hy

theorem nxt_prv' {c : Nat} {Q : Finset Nat} (hA : Above c Q) {y : Nat} (hy : y ∈ insert c Q) :
    nxt c Q (prv c Q y) = y := by
  rcases mem_insert.mp hy with rfl | hy
  · exact nxt_prv_head _ Q
  · exact nxt_prv hA hy

/-- Two arrays of one size that agree at every index are equal. -/
theorem ext_get {a b : Array UInt64} (hs : a.size = b.size) (h : ∀ k < a.size, a[k]! = b[k]!) :
    a = b :=
  Array.ext hs fun k h1 h2 => by
    have := h k h1
    rwa [getElem!_pos a k h1, getElem!_pos b k h2] at this

/-- An array that agrees with `t` on the words of the column, and has the same size, holds the same
column. -/
theorem Col.frame {t t' : Array UInt64} {c : Nat} {Q : Finset Nat} (h : Col t c Q)
    (hsize : t'.size = t.size)
    (hw : ∀ y ∈ insert c Q, ∀ r < 3, t'[3 * y + r]! = t[3 * y + r]!) : Col t' c Q where
  above := h.above
  size := fun y hy => hsize ▸ h.size y hy
  len := by
    have := hw c (mem_insert_self c Q) 0 (by omega)
    simp only [Nat.add_zero] at this
    rw [W, this]; exact h.len
  top := fun q hq => by
    have := hw q (mem_insert_of_mem hq) 0 (by omega)
    simp only [Nat.add_zero] at this
    rw [W, this]; exact h.top q hq
  down := fun y hy => by
    rw [W, hw y hy 2 (by omega)]; exact h.down y hy
  up := fun y hy => by
    rw [W, hw y hy 1 (by omega)]; exact h.up y hy

/-- The reads of `del t q` for a present node `q` of the column. -/
theorem del_get {t : Array UInt64} {c : Nat} {Q : Finset Nat} (h : Col t c Q) {q : Nat}
    (hq : q ∈ Q) (k : Nat) :
    (del t q)[k]! =
      if k = 3 * c then t[3 * c]! - 1
      else if k = 3 * nxt c Q q + 1 then t[3 * q + 1]!
      else if k = 3 * prv c Q q + 2 then t[3 * q + 2]!
      else t[k]! := by
  have hqi : q ∈ insert c Q := mem_insert_of_mem hq
  have hu := h.size _ (prv_mem_insert c Q q)
  have hd := h.size _ (nxt_mem_insert c Q q)
  have hc := h.size _ (mem_insert_self c Q)
  unfold del
  rw [h.up q hqi, h.down q hqi, h.top q hq]
  rw [get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
    get_set _ _ _ _ (by simp only [Array.size_set!]; omega), get_set _ _ _ _ (by omega)]

theorem del_size (t : Array UInt64) (q : Nat) : (del t q).size = t.size := by
  simp [del]

theorem rst_size (t : Array UInt64) (q : Nat) : (rst t q).size = t.size := by
  simp [rst]

/-- Removing a present node leaves the column of the other nodes. -/
theorem del_col {t : Array UInt64} {c : Nat} {Q : Finset Nat} (h : Col t c Q) {q : Nat}
    (hq : q ∈ Q) : Col (del t q) c (Q.erase q) := by
  have hA := h.above
  have hqc : c < q := hA q hq
  set u := prv c Q q
  set d := nxt c Q q
  have hcard : 0 < Q.card := card_pos.mpr ⟨q, hq⟩
  have hget := del_get h hq
  have hsz := del_size t q
  have hAe : Above c (Q.erase q) := fun y hy => hA y (mem_erase.mp hy).2
  have hsub : ∀ y ∈ insert c (Q.erase q), y ∈ insert c Q := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_erase.mp hy).2
  have hyq : ∀ y ∈ insert c (Q.erase q), y ≠ q := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact Nat.ne_of_lt hqc
    · exact (mem_erase.mp hy).1
  refine ⟨hAe, fun y hy => hsz ▸ h.size y (hsub y hy), ?_, ?_, ?_, ?_⟩
  · rw [W, hget, ite_eq_left rfl, UInt64.toNat_sub_of_le]
    · have := h.len
      rw [W] at this
      rw [this, card_erase_of_mem hq]
      simp
    · rw [UInt64.le_iff_toNat_le]
      have := h.len
      rw [W] at this
      simp only [UInt64.toNat_one, this]
      omega
  · intro y hy
    have hyQ := (mem_erase.mp hy).2
    have hyc : c < y := hA y hyQ
    rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    exact h.top y hyQ
  · intro y hy
    rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega)]
    by_cases hyu : y = u
    · rw [ite_eq_left (by rw [hyu])]
      rw [← W, h.down q (mem_insert_of_mem hq), hyu]
      exact (nxt_erase_prv hA hq).symm
    · rw [ite_eq_right (by omega), ← W, h.down y (hsub y hy)]
      refine (nxt_erase_of_ne ?_).symm
      intro he
      apply hyu
      rw [← prv_nxt' hA (hsub y hy), he]
  · intro y hy
    rw [W, hget, ite_eq_right (by omega)]
    by_cases hyd : y = d
    · rw [ite_eq_left (by rw [hyd])]
      rw [← W, h.up q (mem_insert_of_mem hq), hyd]
      exact (prv_erase_nxt hA hq).symm
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ← W, h.up y (hsub y hy)]
      refine (prv_erase_of_ne ?_).symm
      intro he
      apply hyd
      rw [← nxt_prv' hA (hsub y hy), he]

/-- Restoring a node right after removing it returns the array. -/
theorem rst_del {t : Array UInt64} {c : Nat} {Q : Finset Nat} (h : Col t c Q) {q : Nat}
    (hq : q ∈ Q) : rst (del t q) q = t := by
  have hA := h.above
  have hqc : c < q := hA q hq
  have hqi : q ∈ insert c Q := mem_insert_of_mem hq
  set u := prv c Q q
  set d := nxt c Q q
  have hun : u ≠ q := prv_ne hA hq
  have hdn : d ≠ q := nxt_ne hA hq
  have hget := del_get h hq
  have hx : W (del t q) (3 * q) = c := by
    rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    exact h.top q hq
  have hu' : W (del t q) (3 * q + 1) = u := by
    rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    exact h.up q hqi
  have hd' : W (del t q) (3 * q + 2) = d := by
    rw [W, hget, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    exact h.down q hqi
  have hsu := h.size _ (prv_mem_insert c Q q)
  have hsd := h.size _ (nxt_mem_insert c Q q)
  have hsc := h.size _ (mem_insert_self c Q)
  have hsz := del_size t q
  have hval : ∀ y ∈ insert c Q, ∀ r, 3 * y + r < t.size →
      W t (3 * y + r) = q → UInt64.ofNat q = t[3 * y + r]! := by
    intro y _ r _ hw
    rw [W] at hw
    rw [← hw, UInt64.ofNat_toNat]
  apply ext_get (by rw [rst_size, hsz])
  · intro k _
    unfold rst
    rw [hx, hu', hd']
    rw [get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
      get_set _ _ _ _ (by simp only [Array.size_set!]; omega),
      get_set _ _ _ _ (by rw [hsz]; omega)]
    split
    · rename_i hk
      rw [hk, hget, ite_eq_left rfl]
      simp
    split
    · rename_i hk' hk
      rw [hk]
      have := h.up d (nxt_mem_insert c Q q)
      rw [prv_nxt hA hq] at this
      exact hval d (nxt_mem_insert c Q q) 1 (by omega) this
    split
    · rename_i hk'' hk' hk
      rw [hk]
      have := h.down u (prv_mem_insert c Q q)
      rw [nxt_prv hA hq] at this
      exact hval u (prv_mem_insert c Q q) 2 (by omega) this
    · rename_i hk3 hk2 hk1
      rw [hget, ite_eq_right hk1, ite_eq_right hk2, ite_eq_right hk3]

/-- The words that `del t q` writes belong to the column of `q`. -/
theorem del_frame {t : Array UInt64} {c : Nat} {Q : Finset Nat} (h : Col t c Q) {q : Nat}
    (hq : q ∈ Q) (k : Nat) (hk : ∀ y ∈ insert c Q, ∀ r < 3, k ≠ 3 * y + r) :
    (del t q)[k]! = t[k]! := by
  rw [del_get h hq]
  rw [ite_eq_right (by have := hk c (mem_insert_self c Q) 0 (by omega); omega),
    ite_eq_right (by have := hk _ (nxt_mem_insert c Q q) 1 (by omega); omega),
    ite_eq_right (by have := hk _ (prv_mem_insert c Q q) 2 (by omega); omega)]

end Library.Combinatorics.DancingLinks
