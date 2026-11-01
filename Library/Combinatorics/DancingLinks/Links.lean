import LeanExe.Dialect.RepeatWhile
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card

/-! The lists of dancing links, stated pointwise.  A column with header `c` and present nodes `Q`,
all above `c`, is the cyclic list of `c` and the nodes of `Q` in increasing order: `nxt c Q x` is
the least node of `Q` above `x`, or `c`, and `prv c Q x` is the largest node of `Q` below `x`, or
`c`, with the largest node of `Q` before the header.  Removing a node `q` from `Q` changes the
successor of `prv c Q q` to `nxt c Q q` and the predecessor of `nxt c Q q` to `prv c Q q`, and no
other link, which is the write of Knuth's `hide`.  `repeatWhile_inv` proves a property of a loop
from an invariant and a measure below the fuel. -/

namespace Library.Combinatorics.DancingLinks

open Finset

/-- A property that holds at the start of a `repeatWhile`, and that each step under the condition
keeps while it decreases a measure below the fuel, holds at the end, where the condition fails. -/
theorem repeatWhile_inv {α : Type} (fuel : UInt64) (init : α) (cond : α → Bool) (step : α → α)
    (P : α → Prop) (μ : α → Nat) (h0 : P init) (hμ : μ init < fuel.toNat)
    (hstep : ∀ s, P s → cond s = true → P (step s) ∧ μ (step s) < μ s) :
    P (LeanExe.repeatWhile fuel init cond step) ∧
      cond (LeanExe.repeatWhile fuel init cond step) = false := by
  have key : ∀ k s, P s → μ s < k →
      P (LeanExe.repeatWhile.go cond step k s) ∧
        cond (LeanExe.repeatWhile.go cond step k s) = false := by
    intro k
    induction k with
    | zero => intro s _ h; omega
    | succ k ih =>
      intro s hs hk
      rw [LeanExe.repeatWhile.go]
      by_cases hc : cond s = true
      · rw [ite_eq_left hc]
        obtain ⟨hs', hμ'⟩ := hstep s hs hc
        exact ih _ hs' (by omega)
      · rw [ite_eq_right hc]
        exact ⟨hs, by simpa using hc⟩
  exact key _ _ h0 hμ

/-- A property `Q` of the final state of a `repeatWhile`, from an invariant that implies `Q` where
the condition fails. -/
theorem repeatWhile_of_inv {α : Type} (fuel : UInt64) (init : α) (cond : α → Bool) (step : α → α)
    (P : α → Prop) (μ : α → Nat) (Q : α → Prop) (h0 : P init) (hμ : μ init < fuel.toNat)
    (hstep : ∀ s, P s → cond s = true → P (step s) ∧ μ (step s) < μ s)
    (hfin : ∀ s, P s → cond s = false → Q s) : Q (LeanExe.repeatWhile fuel init cond step) := by
  obtain ⟨h1, h2⟩ := repeatWhile_inv fuel init cond step P μ h0 hμ hstep
  exact hfin _ h1 h2

/-- The successor of `x` in the column of header `c` with present nodes `Q`. -/
def nxt (c : Nat) (Q : Finset Nat) (x : Nat) : Nat :=
  if h : (Q.filter (x < ·)).Nonempty then (Q.filter (x < ·)).min' h else c

/-- The predecessor of `x` in the column of header `c` with present nodes `Q`. -/
def prv (c : Nat) (Q : Finset Nat) (x : Nat) : Nat :=
  if x = c then (if h : Q.Nonempty then Q.max' h else c)
  else if h : (Q.filter (· < x)).Nonempty then (Q.filter (· < x)).max' h else c

/-- The nodes of a column lie above its header. -/
def Above (c : Nat) (Q : Finset Nat) : Prop := ∀ q ∈ Q, c < q

theorem nxt_mem (c : Nat) (Q : Finset Nat) (x : Nat) : nxt c Q x = c ∨ nxt c Q x ∈ Q := by
  unfold nxt
  split
  · rename_i h
    exact Or.inr (mem_filter.mp (min'_mem _ h)).1
  · exact Or.inl rfl

theorem prv_mem (c : Nat) (Q : Finset Nat) (x : Nat) : prv c Q x = c ∨ prv c Q x ∈ Q := by
  unfold prv
  split
  · split
    · rename_i h; exact Or.inr (max'_mem _ h)
    · exact Or.inl rfl
  · split
    · rename_i h; exact Or.inr (mem_filter.mp (max'_mem _ h)).1
    · exact Or.inl rfl

theorem nxt_ne {c : Nat} {Q : Finset Nat} (hA : Above c Q) {q : Nat} (hq : q ∈ Q) :
    nxt c Q q ≠ q := by
  unfold nxt
  split
  · rename_i h
    exact Nat.ne_of_gt (mem_filter.mp (min'_mem _ h)).2
  · exact Nat.ne_of_lt (hA q hq)

theorem prv_ne {c : Nat} {Q : Finset Nat} (hA : Above c Q) {q : Nat} (hq : q ∈ Q) :
    prv c Q q ≠ q := by
  have hqc : q ≠ c := Nat.ne_of_gt (hA q hq)
  unfold prv
  rw [ite_eq_right hqc]
  split
  · rename_i h
    exact Nat.ne_of_lt (mem_filter.mp (max'_mem _ h)).2
  · exact Nat.ne_of_lt (hA q hq)

/-- The successor of the predecessor of a present node is the node. -/
theorem nxt_prv {c : Nat} {Q : Finset Nat} (hA : Above c Q) {q : Nat} (hq : q ∈ Q) :
    nxt c Q (prv c Q q) = q := by
  have hqc : q ≠ c := Nat.ne_of_gt (hA q hq)
  unfold prv
  rw [ite_eq_right hqc]
  split
  · rename_i h
    set u := (Q.filter (· < q)).max' h
    have hu : u ∈ Q ∧ u < q := mem_filter.mp (max'_mem _ h)
    unfold nxt
    have hne : (Q.filter (u < ·)).Nonempty := ⟨q, mem_filter.mpr ⟨hq, hu.2⟩⟩
    rw [dite_eq_left hne]
    apply le_antisymm
    · exact min'_le _ _ (mem_filter.mpr ⟨hq, hu.2⟩)
    · apply le_min'
      intro y hy
      obtain ⟨hyQ, huy⟩ := mem_filter.mp hy
      by_contra hlt
      push Not at hlt
      have : y ≤ u := le_max' _ y (mem_filter.mpr ⟨hyQ, hlt⟩)
      omega
  · rename_i h
    unfold nxt
    have hne : (Q.filter (c < ·)).Nonempty := ⟨q, mem_filter.mpr ⟨hq, hA q hq⟩⟩
    rw [dite_eq_left hne]
    apply le_antisymm
    · exact min'_le _ _ (mem_filter.mpr ⟨hq, hA q hq⟩)
    · apply le_min'
      intro y hy
      obtain ⟨hyQ, _⟩ := mem_filter.mp hy
      by_contra hlt
      push Not at hlt
      exact h ⟨y, mem_filter.mpr ⟨hyQ, hlt⟩⟩

/-- The predecessor of the successor of a present node is the node. -/
theorem prv_nxt {c : Nat} {Q : Finset Nat} (hA : Above c Q) {q : Nat} (hq : q ∈ Q) :
    prv c Q (nxt c Q q) = q := by
  unfold nxt
  split
  · rename_i h
    set d := (Q.filter (q < ·)).min' h
    have hd : d ∈ Q ∧ q < d := mem_filter.mp (min'_mem _ h)
    have hdc : d ≠ c := Nat.ne_of_gt (hA d hd.1)
    unfold prv
    rw [ite_eq_right hdc]
    have hne : (Q.filter (· < d)).Nonempty := ⟨q, mem_filter.mpr ⟨hq, hd.2⟩⟩
    rw [dite_eq_left hne]
    apply le_antisymm
    · apply max'_le
      intro y hy
      obtain ⟨hyQ, hyd⟩ := mem_filter.mp hy
      by_contra hlt
      push Not at hlt
      have : d ≤ y := min'_le _ y (mem_filter.mpr ⟨hyQ, hlt⟩)
      omega
    · exact le_max' _ _ (mem_filter.mpr ⟨hq, hd.2⟩)
  · rename_i h
    unfold prv
    rw [ite_eq_left rfl, dite_eq_left ⟨q, hq⟩]
    apply le_antisymm
    · apply max'_le
      intro y hy
      by_contra hlt
      push Not at hlt
      exact h ⟨y, mem_filter.mpr ⟨hy, hlt⟩⟩
    · exact le_max' _ _ hq

/-- After `q` leaves `Q`, the predecessor of `q` precedes the successor of `q`. -/
theorem nxt_erase_prv {c : Nat} {Q : Finset Nat} (hA : Above c Q) {q : Nat} (hq : q ∈ Q) :
    nxt c (Q.erase q) (prv c Q q) = nxt c Q q := by
  have hqc : q ≠ c := Nat.ne_of_gt (hA q hq)
  set u := prv c Q q with hu
  have hun : nxt c Q u = q := nxt_prv hA hq
  have hul : u < q := by
    rw [hu]
    unfold prv
    rw [ite_eq_right hqc]
    split
    · rename_i h; exact (mem_filter.mp (max'_mem _ h)).2
    · exact hA q hq
  have key : (Q.erase q).filter (u < ·) = (Q.filter (q < ·)) := by
    ext y
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨hyq, hyQ⟩, huy⟩
      refine ⟨hyQ, ?_⟩
      have : q ≤ y := by
        rw [← hun]
        unfold nxt
        have hne : (Q.filter (u < ·)).Nonempty := ⟨y, mem_filter.mpr ⟨hyQ, huy⟩⟩
        rw [dite_eq_left hne]
        exact min'_le _ _ (mem_filter.mpr ⟨hyQ, huy⟩)
      omega
    · rintro ⟨hyQ, hqy⟩
      exact ⟨⟨Nat.ne_of_gt hqy, hyQ⟩, Nat.lt_trans hul hqy⟩
  unfold nxt
  rw [key]

/-- After `q` leaves `Q`, the successor of `q` follows the predecessor of `q`. -/
theorem prv_erase_nxt {c : Nat} {Q : Finset Nat} (hA : Above c Q) {q : Nat} (hq : q ∈ Q) :
    prv c (Q.erase q) (nxt c Q q) = prv c Q q := by
  have hqc : q ≠ c := Nat.ne_of_gt (hA q hq)
  set d := nxt c Q q with hd
  have hdp : prv c Q d = q := prv_nxt hA hq
  rcases nxt_mem c Q q with hdc | hdQ
  · -- `q` is the largest node, and the header follows it.
    rw [← hd] at hdc
    rw [hdc] at hdp ⊢
    have hmax : ∀ y ∈ Q, y ≤ q := by
      intro y hy
      rw [← hdp]
      unfold prv
      rw [ite_eq_left rfl, dite_eq_left ⟨q, hq⟩]
      exact le_max' _ _ hy
    unfold prv
    rw [ite_eq_left rfl, ite_eq_right hqc]
    by_cases hne : (Q.erase q).Nonempty
    · rw [dite_eq_left hne]
      have hne' : (Q.filter (· < q)).Nonempty := by
        obtain ⟨y, hy⟩ := hne
        obtain ⟨hyq, hyQ⟩ := mem_erase.mp hy
        exact ⟨y, mem_filter.mpr ⟨hyQ, lt_of_le_of_ne (hmax y hyQ) hyq⟩⟩
      rw [dite_eq_left hne']
      congr 1
      ext y
      simp only [mem_erase, mem_filter]
      constructor
      · rintro ⟨hyq, hyQ⟩; exact ⟨hyQ, lt_of_le_of_ne (hmax y hyQ) hyq⟩
      · rintro ⟨hyQ, hyq⟩; exact ⟨Nat.ne_of_lt hyq, hyQ⟩
    · rw [dite_eq_right hne]
      have hne' : ¬ (Q.filter (· < q)).Nonempty := by
        rintro ⟨y, hy⟩
        obtain ⟨hyQ, hyq⟩ := mem_filter.mp hy
        exact hne ⟨y, mem_erase.mpr ⟨Nat.ne_of_lt hyq, hyQ⟩⟩
      rw [dite_eq_right hne']
  · have hdc : d ≠ c := Nat.ne_of_gt (hA d hdQ)
    have hqd : q < d := by
      rw [hd]
      unfold nxt
      split
      · rename_i h; exact (mem_filter.mp (min'_mem _ h)).2
      · rename_i h
        exact absurd (show nxt c Q q = c by unfold nxt; rw [dite_eq_right h]) (by rw [← hd]; exact hdc)
    have key : (Q.erase q).filter (· < d) = (Q.filter (· < q)) := by
      ext y
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨⟨hyq, hyQ⟩, hyd⟩
        refine ⟨hyQ, ?_⟩
        have : y ≤ q := by
          rw [← hdp]
          unfold prv
          rw [ite_eq_right hdc]
          have hne : (Q.filter (· < d)).Nonempty := ⟨y, mem_filter.mpr ⟨hyQ, hyd⟩⟩
          rw [dite_eq_left hne]
          exact le_max' _ _ (mem_filter.mpr ⟨hyQ, hyd⟩)
        omega
      · rintro ⟨hyQ, hyq⟩
        exact ⟨⟨Nat.ne_of_lt hyq, hyQ⟩, Nat.lt_trans hyq hqd⟩
    unfold prv
    rw [ite_eq_right hdc, ite_eq_right hqc, key]

/-- Removing `q` leaves the successor of every other node unchanged, except that of `q`'s
predecessor. -/
theorem nxt_erase_of_ne {c : Nat} {Q : Finset Nat} {q x : Nat} (hx : nxt c Q x ≠ q) :
    nxt c (Q.erase q) x = nxt c Q x := by
  unfold nxt at hx ⊢
  by_cases h : (Q.filter (x < ·)).Nonempty
  · rw [dite_eq_left h] at hx
    have hmem := min'_mem _ h
    have h' : ((Q.erase q).filter (x < ·)).Nonempty :=
      ⟨_, mem_filter.mpr ⟨mem_erase.mpr ⟨hx, (mem_filter.mp hmem).1⟩, (mem_filter.mp hmem).2⟩⟩
    rw [dite_eq_left h', dite_eq_left h]
    apply le_antisymm
    · exact min'_le _ _ (mem_filter.mpr ⟨mem_erase.mpr ⟨hx, (mem_filter.mp hmem).1⟩,
        (mem_filter.mp hmem).2⟩)
    · apply le_min'
      intro y hy
      obtain ⟨hy1, hy2⟩ := mem_filter.mp hy
      exact min'_le _ _ (mem_filter.mpr ⟨(mem_erase.mp hy1).2, hy2⟩)
  · have h' : ¬ ((Q.erase q).filter (x < ·)).Nonempty := by
      rintro ⟨y, hy⟩
      obtain ⟨hy1, hy2⟩ := mem_filter.mp hy
      exact h ⟨y, mem_filter.mpr ⟨(mem_erase.mp hy1).2, hy2⟩⟩
    rw [dite_eq_right h', dite_eq_right h]

/-- Removing `q` leaves the predecessor of every other node unchanged, except that of `q`'s
successor. -/
theorem prv_erase_of_ne {c : Nat} {Q : Finset Nat} {q x : Nat} (hx : prv c Q x ≠ q) :
    prv c (Q.erase q) x = prv c Q x := by
  by_cases hxc : x = c
  · have e1 : prv c (Q.erase q) x = if h : (Q.erase q).Nonempty then (Q.erase q).max' h else c := by
      unfold prv; rw [ite_eq_left hxc]
    have e2 : prv c Q x = if h : Q.Nonempty then Q.max' h else c := by
      unfold prv; rw [ite_eq_left hxc]
    rw [e2] at hx
    rw [e1, e2]
    by_cases h : Q.Nonempty
    · rw [dite_eq_left h] at hx
      have hmem := max'_mem _ h
      have h' : (Q.erase q).Nonempty := ⟨_, mem_erase.mpr ⟨hx, hmem⟩⟩
      rw [dite_eq_left h', dite_eq_left h]
      apply le_antisymm
      · apply max'_le
        intro y hy
        exact le_max' _ _ (mem_erase.mp hy).2
      · exact le_max' _ _ (mem_erase.mpr ⟨hx, hmem⟩)
    · have h' : ¬ (Q.erase q).Nonempty := by
        rintro ⟨y, hy⟩
        exact h ⟨y, (mem_erase.mp hy).2⟩
      rw [dite_eq_right h', dite_eq_right h]
  · have e1 : prv c (Q.erase q) x =
        if h : ((Q.erase q).filter (· < x)).Nonempty then ((Q.erase q).filter (· < x)).max' h
        else c := by
      unfold prv; rw [ite_eq_right hxc]
    have e2 : prv c Q x =
        if h : (Q.filter (· < x)).Nonempty then (Q.filter (· < x)).max' h else c := by
      unfold prv; rw [ite_eq_right hxc]
    rw [e2] at hx
    rw [e1, e2]
    by_cases h : (Q.filter (· < x)).Nonempty
    · rw [dite_eq_left h] at hx
      have hmem := max'_mem _ h
      have hm := mem_filter.mp hmem
      have h' : ((Q.erase q).filter (· < x)).Nonempty :=
        ⟨_, mem_filter.mpr ⟨mem_erase.mpr ⟨hx, hm.1⟩, hm.2⟩⟩
      rw [dite_eq_left h', dite_eq_left h]
      apply le_antisymm
      · apply max'_le
        intro y hy
        obtain ⟨hy1, hy2⟩ := mem_filter.mp hy
        exact le_max' _ _ (mem_filter.mpr ⟨(mem_erase.mp hy1).2, hy2⟩)
      · exact le_max' _ _ (mem_filter.mpr ⟨mem_erase.mpr ⟨hx, hm.1⟩, hm.2⟩)
    · have h' : ¬ ((Q.erase q).filter (· < x)).Nonempty := by
        rintro ⟨y, hy⟩
        obtain ⟨hy1, hy2⟩ := mem_filter.mp hy
        exact h ⟨y, mem_filter.mpr ⟨(mem_erase.mp hy1).2, hy2⟩⟩
      rw [dite_eq_right h', dite_eq_right h]

end Library.Combinatorics.DancingLinks
