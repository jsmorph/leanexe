import Library.Sorting.Find.Program
import Library.Sorting.Find.Spec
import Library.Sorting.Quicksort.Proof
import Library.Sorting.Sorted

/-! The proof that FIND returns the word of rank `k`.  Steps Q3 to Q6 put the partitioning word `K`
at its final position `j`, every word of the subfile before `j` at most `K`, and every word after
`j` at least `K` (`part_spec`).  Their exchanges stay within the subfile, so the words outside it
keep their places and every word inside it comes from the subfile (`Frame`, `FromSeg`).  FIND then
leaves the word at `k` at least every word before it and at most every word after it in the subfile
it started with (`find_spec`).  Sorting the words before `k` and the words after `k` around it gives
a nondecreasing permutation of the array, the only one, so the word at `k` is the word of rank `k`
(`rank_of_around`). -/

namespace Library.Sorting.Find

open Library.Sorting.Heapsort (swap swap_size swap_get wle_trans wle_of_lt wle_of_not_lt wle_refl)
open Library.Sorting.Quicksort (scanUp scanDown scanUp_ge scanDown_bounds part part_fst part_perm
  succ_toNat pred_toNat span span_eq)

/-! ### Scans -/

/-- Step Q3 from `i ≤ e` stops at a position `u` in `[i, e]` after words below `K`, at a word not
below `K` unless `u = e`. -/
theorem scanUp_spec (K e : UInt64) (a : Array UInt64) (i : UInt64) (hi : i ≤ e) :
    i.toNat ≤ (scanUp K e i a).toNat ∧ (scanUp K e i a).toNat ≤ e.toNat ∧
      (∀ p, i.toNat ≤ p → p < (scanUp K e i a).toNat → a[p]! < K) ∧
      (scanUp K e i a < e → ¬ a[(scanUp K e i a).toNat]! < K) := by
  by_cases h : i < e
  · by_cases hlt : a[i.toNat]! < K
    · have heq : scanUp K e i a = scanUp K e (i + 1) a := by
        rw [scanUp.eq_def K e i a, ite_eq_left h, ite_eq_left hlt]
      have hle : i + 1 ≤ e := by
        rw [UInt64.le_iff_toNat_le, succ_toNat h]; exact UInt64.lt_iff_toNat_lt.mp h
      have ih := scanUp_spec K e a (i + 1) hle
      rw [succ_toNat h] at ih
      rw [heq]
      refine ⟨by omega, ih.2.1, fun p hp hpu => ?_, ih.2.2.2⟩
      by_cases hpi : p = i.toNat
      · subst hpi; exact hlt
      · exact ih.2.2.1 p (by omega) hpu
    · have heq : scanUp K e i a = i := by
        rw [scanUp.eq_def K e i a, ite_eq_left h, ite_eq_right hlt]
      rw [heq]
      exact ⟨Nat.le_refl _, UInt64.le_iff_toNat_le.mp hi,
        fun p hp hpu => absurd hpu (Nat.not_lt.mpr hp), fun _ => hlt⟩
  · have heq : scanUp K e i a = i := by rw [scanUp.eq_def K e i a, ite_eq_right h]
    rw [heq]
    exact ⟨Nat.le_refl _, UInt64.le_iff_toNat_le.mp hi,
      fun p hp hpu => absurd hpu (Nat.not_lt.mpr hp), fun hlt => absurd hlt h⟩
termination_by (e - i).toNat
decreasing_by
  have h : i < e := by assumption
  simp only [UInt64.lt_iff_toNat_lt] at h
  simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
  have := UInt64.toNat_lt e
  omega

/-- Step Q4 from `j ≥ l` stops at a position `d` in `[l, j]` before words above `K`, at a word not
above `K` unless `d = l`. -/
theorem scanDown_spec (K l : UInt64) (a : Array UInt64) (j : UInt64) (hj : l ≤ j) :
    l.toNat ≤ (scanDown K l j a).toNat ∧ (scanDown K l j a).toNat ≤ j.toNat ∧
      (∀ p, (scanDown K l j a).toNat < p → p ≤ j.toNat → K < a[p]!) ∧
      (l < scanDown K l j a → ¬ K < a[(scanDown K l j a).toNat]!) := by
  by_cases h : l < j
  · by_cases hlt : K < a[j.toNat]!
    · have heq : scanDown K l j a = scanDown K l (j - 1) a := by
        rw [scanDown.eq_def K l j a, ite_eq_left h, ite_eq_left hlt]
      have hle : l ≤ j - 1 := by
        rw [UInt64.le_iff_toNat_le, pred_toNat h]; rw [UInt64.lt_iff_toNat_lt] at h; omega
      have ih := scanDown_spec K l a (j - 1) hle
      rw [pred_toNat h] at ih
      have hjn := UInt64.lt_iff_toNat_lt.mp h
      rw [heq]
      refine ⟨ih.1, by omega, fun p hp hpj => ?_, ih.2.2.2⟩
      by_cases hpj' : p = j.toNat
      · subst hpj'; exact hlt
      · exact ih.2.2.1 p hp (by omega)
    · have heq : scanDown K l j a = j := by
        rw [scanDown.eq_def K l j a, ite_eq_left h, ite_eq_right hlt]
      rw [heq]
      exact ⟨UInt64.le_iff_toNat_le.mp hj, Nat.le_refl _,
        fun p hp hpj => absurd hpj (Nat.not_le.mpr hp), fun _ => hlt⟩
  · have heq : scanDown K l j a = j := by rw [scanDown.eq_def K l j a, ite_eq_right h]
    rw [heq]
    exact ⟨UInt64.le_iff_toNat_le.mp hj, Nat.le_refl _,
      fun p hp hpj => absurd hpj (Nat.not_le.mpr hp), fun hlt => absurd hlt h⟩
termination_by j.toNat
decreasing_by
  have h : l < j := by assumption
  simp only [UInt64.lt_iff_toNat_lt] at h
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt j
  omega

/-! ### Changes within a subfile -/

/-- `b` holds the words of `a` outside `[l, e)`. -/
def Frame (l e : Nat) (a b : Array UInt64) : Prop := ∀ q, (q < l ∨ e ≤ q) → b[q]! = a[q]!

/-- Each word of `b` in `[l, e)` is a word of `a` in `[l, e)`. -/
def FromSeg (l e : Nat) (a b : Array UInt64) : Prop :=
  ∀ q, l ≤ q → q < e → ∃ q', l ≤ q' ∧ q' < e ∧ b[q]! = a[q']!

theorem Frame.trans {l e : Nat} {a b c : Array UInt64} (h1 : Frame l e a b) (h2 : Frame l e b c) :
    Frame l e a c :=
  fun q hq => (h2 q hq).trans (h1 q hq)

theorem FromSeg.trans {l e : Nat} {a b c : Array UInt64} (h1 : FromSeg l e a b)
    (h2 : FromSeg l e b c) : FromSeg l e a c := by
  intro q hlq hqe
  obtain ⟨q', h1', h2', hb⟩ := h2 q hlq hqe
  obtain ⟨q'', h1'', h2'', ha⟩ := h1 q' h1' h2'
  exact ⟨q'', h1'', h2'', hb.trans ha⟩

/-- A change within `[l', e')` is a change within every subfile `[l, e)` that contains it. -/
theorem Frame.widen {l e l' e' : Nat} {a b : Array UInt64} (hl : l ≤ l') (he : e' ≤ e)
    (h : Frame l' e' a b) : Frame l e a b :=
  fun q hq => h q (by omega)

theorem FromSeg.widen {l e l' e' : Nat} {a b : Array UInt64} (hl : l ≤ l') (he : e' ≤ e)
    (hf : Frame l' e' a b) (h : FromSeg l' e' a b) : FromSeg l e a b := by
  intro q hlq hqe
  by_cases hq : l' ≤ q ∧ q < e'
  · obtain ⟨q', h1, h2, hb⟩ := h q hq.1 hq.2
    exact ⟨q', by omega, by omega, hb⟩
  · exact ⟨q, hlq, hqe, hf q (by omega)⟩

/-- An exchange of two positions of `[l, e)` is a change within `[l, e)`. -/
theorem swap_within (a : Array UInt64) (u d : UInt64) (l e : Nat)
    (hu : l ≤ u.toNat ∧ u.toNat < e) (hd : l ≤ d.toNat ∧ d.toNat < e) (hea : e ≤ a.size) :
    Frame l e a (swap u d a) ∧ FromSeg l e a (swap u d a) := by
  constructor
  · intro q hq
    rw [swap_get a u d (by omega) (by omega)]
    have h1 : q ≠ d.toNat := by omega
    have h2 : q ≠ u.toNat := by omega
    rw [ite_eq_right h1, ite_eq_right h2]
  · intro q hlq hqe
    rw [swap_get a u d (by omega) (by omega)]
    by_cases h1 : q = d.toNat
    · rw [ite_eq_left h1]; exact ⟨u.toNat, hu.1, hu.2, rfl⟩
    · rw [ite_eq_right h1]
      by_cases h2 : q = u.toNat
      · rw [ite_eq_left h2]; exact ⟨d.toNat, hd.1, hd.2, rfl⟩
      · rw [ite_eq_right h2]; exact ⟨q, hlq, hqe, rfl⟩

/-! ### The partition -/

/-- An exchange leaves the words at other positions in place. -/
theorem swap_get_ne (a : Array UInt64) (u d : UInt64) (hu : u.toNat < a.size)
    (hd : d.toNat < a.size) (q : Nat) (h1 : q ≠ u.toNat) (h2 : q ≠ d.toNat) :
    (swap u d a)[q]! = a[q]! := by
  rw [swap_get a u d hu hd, ite_eq_right h2, ite_eq_right h1]

/-- An exchange puts the word of `u` at `d`. -/
theorem swap_get_right (a : Array UInt64) (u d : UInt64) (hu : u.toNat < a.size)
    (hd : d.toNat < a.size) : (swap u d a)[d.toNat]! = a[u.toNat]! := by
  rw [swap_get a u d hu hd, ite_eq_left rfl]

/-- An exchange of distinct positions puts the word of `d` at `u`. -/
theorem swap_get_left (a : Array UInt64) (u d : UInt64) (hu : u.toNat < a.size)
    (hd : d.toNat < a.size) (h : u.toNat ≠ d.toNat) : (swap u d a)[u.toNat]! = a[d.toNat]! := by
  rw [swap_get a u d hu hd, ite_eq_right h, ite_eq_left rfl]

/-- Steps Q3 to Q6 from positions `l ≤ i < j ≤ e`, with `K` at `l`, every word of `(l, i]` at most
`K`, and every word of `[j, e)` at least `K`, put `K` at the final position `m`, every word of
`[l, m)` at most `K`, and every word of `(m, e)` at least `K`, by a change within `[l, e)`. -/
theorem part_spec (K l e : UInt64) (a : Array UInt64) (i j : UInt64) (hli : l ≤ i) (hij : i < j)
    (hje : j ≤ e) (hea : e.toNat ≤ a.size) (hK : a[l.toNat]! = K)
    (hlo : ∀ p, l.toNat < p → p ≤ i.toNat → a[p]! ≤ K)
    (hhi : ∀ p, j.toNat ≤ p → p < e.toNat → K ≤ a[p]!) :
    (part K l e i j a).2[(part K l e i j a).1.toNat]! = K ∧
      (∀ p, l.toNat ≤ p → p < (part K l e i j a).1.toNat → (part K l e i j a).2[p]! ≤ K) ∧
      (∀ p, (part K l e i j a).1.toNat < p → p < e.toNat → K ≤ (part K l e i j a).2[p]!) ∧
      Frame l.toNat e.toNat a (part K l e i j a).2 ∧
      FromSeg l.toNat e.toNat a (part K l e i j a).2 := by
  have hl0 := UInt64.le_iff_toNat_le.mp hli
  have hij0 := UInt64.lt_iff_toNat_lt.mp hij
  have hje0 := UInt64.le_iff_toNat_le.mp hje
  have hlj : l ≤ j - 1 := by
    rw [UInt64.le_iff_toNat_le, pred_toNat hij]; omega
  have hie : i + 1 ≤ e := by
    rw [UInt64.le_iff_toNat_le, succ_toNat hij]; omega
  have hd := scanDown_spec K l a (j - 1) hlj
  have hu := scanUp_spec K e a (i + 1) hie
  rw [pred_toNat hij] at hd
  rw [succ_toNat hij] at hu
  rw [part, ite_eq_left hij]
  split
  · rename_i h4
    have h5 := UInt64.lt_iff_toNat_lt.mp h4
    have hua : (scanUp K e (i + 1) a).toNat < a.size := by omega
    have hda : (scanDown K l (j - 1) a).toNat < a.size := by omega
    have hsw := swap_within a (scanUp K e (i + 1) a) (scanDown K l (j - 1) a) l.toNat e.toNat
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hea
    have hne := swap_get_ne a (scanUp K e (i + 1) a) (scanDown K l (j - 1) a) hua hda
    have hdl : l < scanDown K l (j - 1) a := UInt64.lt_iff_toNat_lt.mpr (by omega)
    have hue : scanUp K e (i + 1) a < e := UInt64.lt_iff_toNat_lt.mpr (by omega)
    have ih := part_spec K l e (swap (scanUp K e (i + 1) a) (scanDown K l (j - 1) a) a)
      (scanUp K e (i + 1) a) (scanDown K l (j - 1) a)
      (UInt64.le_iff_toNat_le.mpr (by omega)) h4 (UInt64.le_iff_toNat_le.mpr (by omega))
      (by rw [swap_size]; exact hea)
      (by rw [hne l.toNat (by omega) (by omega), hK])
      (fun p hp hpu => by
        by_cases hpu' : p = (scanUp K e (i + 1) a).toNat
        · rw [hpu', swap_get_left a _ _ hua hda (by omega)]
          exact wle_of_not_lt (hd.2.2.2 hdl)
        · rw [hne p hpu' (by omega)]
          by_cases hpi : p ≤ i.toNat
          · exact hlo p hp hpi
          · exact wle_of_lt (hu.2.2.1 p (by omega) (by omega)))
      (fun p hdp hpe => by
        by_cases hpd : p = (scanDown K l (j - 1) a).toNat
        · rw [hpd, swap_get_right a _ _ hua hda]
          exact wle_of_not_lt (hu.2.2.2 hue)
        · rw [hne p (by omega) hpd]
          by_cases hpj : p < j.toNat
          · exact wle_of_lt (hd.2.2.1 p (by omega) (by omega))
          · exact hhi p (by omega) hpe)
    exact ⟨ih.1, ih.2.1, ih.2.2.1, hsw.1.trans ih.2.2.2.1, hsw.2.trans ih.2.2.2.2⟩
  · rename_i h4
    dsimp only
    have h5 : (scanDown K l (j - 1) a).toNat ≤ (scanUp K e (i + 1) a).toNat :=
      UInt64.le_iff_toNat_le.mp (wle_of_not_lt h4)
    have hla : l.toNat < a.size := by omega
    have hda : (scanDown K l (j - 1) a).toNat < a.size := by omega
    have hsw := swap_within a l (scanDown K l (j - 1) a) l.toNat e.toNat
      ⟨Nat.le_refl _, by omega⟩ ⟨by omega, by omega⟩ hea
    have hne := swap_get_ne a l (scanDown K l (j - 1) a) hla hda
    refine ⟨by rw [swap_get_right a _ _ hla hda, hK], fun p hlp hpd => ?_, fun p hdp hpe => ?_,
      hsw.1, hsw.2⟩
    · by_cases hpl : p = l.toNat
      · rw [hpl, swap_get_left a _ _ hla hda (by omega)]
        exact wle_of_not_lt (hd.2.2.2 (UInt64.lt_iff_toNat_lt.mpr (by omega)))
      · rw [hne p hpl (by omega)]
        by_cases hpi : p ≤ i.toNat
        · exact hlo p (by omega) hpi
        · exact wle_of_lt (hu.2.2.1 p (by omega) (by omega))
    · rw [hne p (by omega) (by omega)]
      by_cases hpj : p < j.toNat
      · exact wle_of_lt (hd.2.2.1 p hdp (by omega))
      · exact hhi p (by omega) hpe
termination_by (j - i).toNat
decreasing_by
  have h1 : i < j := by assumption
  have h4 : scanUp K e (i + 1) a < scanDown K l (j - 1) a := by assumption
  have h2 := scanUp_ge K e a (i + 1)
  have h3 := (scanDown_bounds K l a (j - 1)).1
  rw [succ_toNat h1] at h2
  rw [pred_toNat h1] at h3
  simp only [UInt64.lt_iff_toNat_lt] at h1 h4
  simp only [UInt64.toNat_sub]
  have := UInt64.toNat_lt j
  omega

/-! ### FIND -/

/-- `b` is `a` partitioned within `[l, e)` around the word `a[l]`, which `b` holds at `m`. -/
structure Parted (l e : Nat) (a : Array UInt64) (m : Nat) (b : Array UInt64) : Prop where
  lo : l ≤ m
  hi : m < e
  size : b.size = a.size
  perm : b.toList.Perm a.toList
  at_m : b[m]! = a[l]!
  below : ∀ p, l ≤ p → p < m → b[p]! ≤ a[l]!
  above : ∀ p, m < p → p < e → a[l]! ≤ b[p]!
  frame : Frame l e a b
  fromSeg : FromSeg l e a b

/-- The partition of a subfile `[l, e)` that ends within the array, around its first word. -/
theorem part_full (l e : UInt64) (a : Array UInt64) (hc : l < e) (he : e.toNat ≤ a.size) :
    Parted l.toNat e.toNat a (part a[l.toNat]! l e l e a).1.toNat
      (part a[l.toNat]! l e l e a).2 := by
  have hll : l ≤ l := UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)
  have hf := part_fst a[l.toNat]! l e a l e hll hc
  have hp := part_perm a[l.toNat]! l e l e a hll he
  have hs := part_spec a[l.toNat]! l e a l e hll hc (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _))
    he rfl (fun p h1 h2 => absurd h2 (Nat.not_le.mpr h1))
    (fun p h1 h2 => absurd h2 (Nat.not_lt.mpr h1))
  exact ⟨hf.1, hf.2, hp.1, hp.2, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩

/-- The word of `R` at `k` is at least every word of `[l, k)` and at most every word of `(k, e)`. -/
def Around (k l e : Nat) (R : Array UInt64) : Prop :=
  (∀ p, l ≤ p → p < k → R[p]! ≤ R[k]!) ∧ (∀ p, k < p → p < e → R[k]! ≤ R[p]!)

/-- FIND on a subfile `[l, e)` that ends within the array permutes the array by a change within the
subfile, and when the subfile holds `k`, it leaves at `k` a word at least every word of `[l, k)` and
at most every word of `(k, e)`. -/
theorem find_spec (k l e : UInt64) (a : Array UInt64) :
    e.toNat ≤ a.size →
      (find k l e a).size = a.size ∧ (find k l e a).toList.Perm a.toList ∧
        Frame l.toNat e.toNat a (find k l e a) ∧ FromSeg l.toNat e.toNat a (find k l e a) ∧
        (l.toNat ≤ k.toNat → k.toNat < e.toNat →
          Around k.toNat l.toNat e.toNat (find k l e a)) := by
  fun_induction find k l e a with
  | case1 l e a hc r hk ih =>
    intro he
    have hp : Parted l.toNat e.toNat a r.1.toNat r.2 := part_full l e a hc.1 he
    have hm := hp.hi
    have hk0 := UInt64.lt_iff_toNat_lt.mp hk
    obtain ⟨hs, hpm, hfr, hfs, hA⟩ := ih (by rw [hp.size]; omega)
    refine ⟨hs.trans hp.size, hpm.trans hp.perm,
      hp.frame.trans (hfr.widen (Nat.le_refl _) (by omega)),
      hp.fromSeg.trans (hfs.widen (Nat.le_refl _) (by omega) hfr), fun hlk hke => ?_⟩
    obtain ⟨hA1, hA2⟩ := hA hlk hk0
    refine ⟨hA1, fun p hkp hpe => ?_⟩
    by_cases hpr : p < r.1.toNat
    · exact hA2 p hkp hpr
    · obtain ⟨q, hq1, hq2, hRq⟩ := hfs k.toNat hlk hk0
      have hRp : (find k l r.1 r.2)[p]! = r.2[p]! := hfr p (Or.inr (by omega))
      rw [hRq, hRp]
      refine wle_trans (hp.below q hq1 hq2) ?_
      by_cases hpm' : p = r.1.toNat
      · rw [hpm', hp.at_m]; exact wle_refl _
      · exact hp.above p (by omega) hpe
  | case2 l e a hc r hk hk2 ih =>
    intro he
    have hp : Parted l.toNat e.toNat a r.1.toNat r.2 := part_full l e a hc.1 he
    have hm := hp.hi
    have hlm := hp.lo
    have hj1 : (r.1 + 1).toNat = r.1.toNat + 1 := succ_toNat (UInt64.lt_iff_toNat_lt.mpr hm)
    have hk0 := UInt64.lt_iff_toNat_lt.mp hk2
    obtain ⟨hs, hpm, hfr, hfs, hA⟩ := ih (by rw [hp.size]; exact he)
    rw [hj1] at hfr hfs hA
    refine ⟨hs.trans hp.size, hpm.trans hp.perm,
      hp.frame.trans (hfr.widen (by omega) (Nat.le_refl _)),
      hp.fromSeg.trans (hfs.widen (by omega) (Nat.le_refl _) hfr), fun hlk hke => ?_⟩
    obtain ⟨hA1, hA2⟩ := hA (by omega) hke
    refine ⟨fun p hlp hpk => ?_, hA2⟩
    by_cases hpr : r.1.toNat + 1 ≤ p
    · exact hA1 p hpr hpk
    · obtain ⟨q, hq1, hq2, hRq⟩ := hfs k.toNat (by omega) hke
      have hRp : (find k (r.1 + 1) e r.2)[p]! = r.2[p]! := hfr p (Or.inl (by omega))
      rw [hRq, hRp]
      refine wle_trans ?_ (hp.above q (by omega) hq2)
      by_cases hpm' : p = r.1.toNat
      · rw [hpm', hp.at_m]; exact wle_refl _
      · exact hp.below p hlp (by omega)
  | case3 l e a hc r hk hk2 =>
    intro he
    have hp : Parted l.toNat e.toNat a r.1.toNat r.2 := part_full l e a hc.1 he
    have h1 : ¬ k.toNat < r.1.toNat := fun h => hk (UInt64.lt_iff_toNat_lt.mpr h)
    have h2 : ¬ r.1.toNat < k.toNat := fun h => hk2 (UInt64.lt_iff_toNat_lt.mpr h)
    have hkr : k.toNat = r.1.toNat := by omega
    refine ⟨hp.size, hp.perm, hp.frame, hp.fromSeg,
      fun _ _ => ⟨fun p hlp hpk => ?_, fun p hkp hpe => ?_⟩⟩
    · rw [hkr, hp.at_m]; exact hp.below p hlp (by omega)
    · rw [hkr, hp.at_m]; exact hp.above p (by omega) hpe
  | case4 l e a hc =>
    intro he
    refine ⟨rfl, List.Perm.refl _, fun q _ => rfl, fun q hlq hqe => ⟨q, hlq, hqe, rfl⟩,
      fun hlk hke => ?_⟩
    have hle : e.toNat ≤ l.toNat + 1 := by
      by_cases hle : l < e
      · have h1 : ¬ 1 < e - l := fun h => hc ⟨hle, h⟩
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (wle_of_lt hle)] at h1
        simp only [UInt64.reduceToNat] at h1
        omega
      · rw [UInt64.lt_iff_toNat_lt] at hle; omega
    exact ⟨fun p hlp hpk => absurd hpk (by omega), fun p hkp hpe => absurd hpe (by omega)⟩

/-! ### The word of rank `k` -/

/-- In a permutation `R` of `xs` whose word at `k` is at least every earlier word and at most every
later word, that word is the word at `k` of `xs` sorted: sorting the words before `k` and the words
after `k` around it gives a nondecreasing permutation of `xs`, which is `List.mergeSort` of it. -/
theorem rank_of_around (xs R : Array UInt64) (k : Nat) (hperm : R.toList.Perm xs.toList)
    (hk : k < R.size) (hA : Around k 0 R.size R) :
    (xs.toList.mergeSort fun a b => a ≤ b).toArray[k]! = R[k]! := by
  have hkL : k < R.toList.length := by simpa using hk
  have hx : R[k]! = R.toList[k] := by rw [getElem!_pos R k hk, Array.getElem_toList]
  have hpre : ∀ y ∈ R.toList.take k, y ≤ R[k]! := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    rw [List.getElem_take]
    have hik : i < k := by simp at hi; omega
    have := hA.1 i (Nat.zero_le _) hik
    rwa [getElem!_pos R i (by omega), ← Array.getElem_toList] at this
  have hsuf : ∀ y ∈ R.toList.drop (k + 1), R[k]! ≤ y := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    rw [List.getElem_drop]
    have hik : k + 1 + i < R.size := by simp at hi; omega
    have := hA.2 (k + 1 + i) (by omega) hik
    rwa [getElem!_pos R (k + 1 + i) hik, ← Array.getElem_toList] at this
  have hS : ((R.toList.take k).mergeSort (fun a b => a ≤ b) ++
      R[k]! :: (R.toList.drop (k + 1)).mergeSort (fun a b => a ≤ b)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨Library.Sorting.pairwise_mergeSort_le _,
      ⟨fun y hy => hsuf y ((List.mergeSort_perm _ _).mem_iff.mp hy),
        Library.Sorting.pairwise_mergeSort_le _⟩, fun y hy z hz => ?_⟩
    have hy' := hpre y ((List.mergeSort_perm _ _).mem_iff.mp hy)
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hy'
    · exact wle_trans hy' (hsuf z ((List.mergeSort_perm _ _).mem_iff.mp hz))
  have hsplit : R.toList.take k ++ R[k]! :: R.toList.drop (k + 1) = R.toList := by
    rw [hx, ← List.drop_eq_getElem_cons hkL, List.take_append_drop]
  have hP := (List.mergeSort_perm (R.toList.take k) (fun a b => a ≤ b)).append
    ((List.mergeSort_perm (R.toList.drop (k + 1)) (fun a b => a ≤ b)).cons R[k]!)
  rw [hsplit] at hP
  rw [← Library.Sorting.eq_mergeSort_of_sorted_perm hS (hP.trans hperm)]
  have hlen : ((R.toList.take k).mergeSort fun a b => a ≤ b).length = k := by
    rw [List.length_mergeSort, List.length_take]; omega
  rw [getElem!_pos _ k (by
      simp only [List.size_toArray, List.length_append, List.length_cons, hlen]; omega),
    List.getElem_toArray, List.getElem_append_right (Nat.le_of_eq hlen)]
  simp [hlen]

/-- FIND computes the specification on every array that memory can hold. -/
theorem select_eq (xs : Array UInt64) (k : UInt64) (hsize : xs.size < 2 ^ 64) :
    select xs k = expected xs k := by
  have hN : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold select expected
  dsimp only
  by_cases hk : k.toNat < xs.size
  · have hkn : k < xs.size.toUInt64 := UInt64.lt_iff_toNat_lt.mpr (by rw [hN]; exact hk)
    rw [ite_eq_left hkn]
    obtain ⟨hs, hp, -, -, hA⟩ := find_spec k 0 xs.size.toUInt64 xs (by rw [hN])
    have h0 : (0 : UInt64).toNat = 0 := by simp only [UInt64.reduceToNat]
    rw [h0, hN] at hA
    exact (rank_of_around xs _ k.toNat hp (by rw [hs]; exact hk)
      (by rw [hs]; exact hA (Nat.zero_le _) hk)).symm
  · have hkn : ¬ k < xs.size.toUInt64 := fun h => hk (by
      have := UInt64.lt_iff_toNat_lt.mp h
      rwa [hN] at this)
    rw [ite_eq_right hkn]
    exact (getElem!_neg _ k.toNat (by
      simp only [List.size_toArray, List.length_mergeSort, Array.length_toList]; exact hk)).symm

end Library.Sorting.Find
