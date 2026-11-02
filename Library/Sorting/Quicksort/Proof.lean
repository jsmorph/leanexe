import Library.Sorting.Quicksort.Program
import Library.Sorting.Quicksort.Spec
import Library.Sorting.Heapsort.Proof
import Library.Sorting.StraightInsertion.Proof

/-! The proof that quicksort returns the array's elements in nondecreasing order.  Step Q9 sorts
every array by straight insertion, so the proof needs only that steps Q1 to Q8 return a permutation
of the input.  Every exchange of `part` lies within the array when the subfile ends within it
(`part_perm`), and every subfile that `stages` takes from the stack ends within the array
(`stages_perm`).  The order that the partitions establish determines the running time of step Q9
and has no part in the proof. -/

namespace Library.Sorting.Quicksort

open Library.Sorting.Heapsort (swap swap_size swap_perm)
open Library.Sorting.StraightInsertion (straightInsertion)

/-- Steps Q3 to Q6 return a permutation of the array when the subfile ends within it. -/
theorem part_perm (K l e : UInt64) (i j : UInt64) (a : Array UInt64) (hl : l ≤ i)
    (hj : j.toNat ≤ a.size) :
    (part K l e i j a).2.size = a.size ∧ (part K l e i j a).2.toList.Perm a.toList := by
  rw [part]
  split
  · rename_i hij
    have hlj : l ≤ j - 1 := by
      rw [UInt64.le_iff_toNat_le, pred_toNat hij]; rw [UInt64.le_iff_toNat_le] at hl
      rw [UInt64.lt_iff_toNat_lt] at hij; omega
    have hd := scanDown_bounds K l a (j - 1)
    rw [pred_toNat hij] at hd
    have hjn := UInt64.lt_iff_toNat_lt.mp hij
    split
    · rename_i h4
      have hu := scanUp_ge K e a (i + 1)
      rw [succ_toNat hij] at hu
      have hl' : l ≤ scanUp K e (i + 1) a := by
        rw [UInt64.le_iff_toNat_le]; rw [UInt64.le_iff_toNat_le] at hl; omega
      have h5 := UInt64.lt_iff_toNat_lt.mp h4
      have hs := swap_size a (scanUp K e (i + 1) a) (scanDown K l (j - 1) a)
      have ih := part_perm K l e (scanUp K e (i + 1) a) (scanDown K l (j - 1) a)
        (swap (scanUp K e (i + 1) a) (scanDown K l (j - 1) a) a) hl' (by rw [hs]; omega)
      exact ⟨ih.1.trans hs, ih.2.trans (swap_perm _ _ _ (by omega) (by omega))⟩
    · have hld := hd.2 hlj
      exact ⟨swap_size _ _ _, swap_perm _ _ _ (by omega) (by omega)⟩
  · exact ⟨rfl, List.Perm.refl _⟩
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

/-- The partition of a subfile `[l, e)` that ends within the array puts `K` at a position of the
subfile and permutes the array. -/
theorem part_within (l e : UInt64) (a : Array UInt64) (hc : l < e) (he : e.toNat ≤ a.size) :
    l.toNat ≤ (part a[l.toNat]! l e l e a).1.toNat ∧
      (part a[l.toNat]! l e l e a).1.toNat < e.toNat ∧
      (part a[l.toNat]! l e l e a).2.size = a.size ∧
      (part a[l.toNat]! l e l e a).2.toList.Perm a.toList :=
  have hll : l ≤ l := UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)
  have hf := part_fst a[l.toNat]! l e a l e hll hc
  have hp := part_perm a[l.toNat]! l e l e a hll he
  ⟨hf.1, hf.2, hp.1, hp.2⟩

theorem get_set_le (st : Array UInt64) (i : Nat) (v : UInt64) :
    (st.set! i v)[i]!.toNat ≤ v.toNat := by
  by_cases h : i < st.size
  · rw [get_set_self st i v h]
  · rw [getElem!_neg _ i (by simpa using h)]
    exact Nat.zero_le _

/-- A push keeps every subfile on the stack within `n` words when the pushed one ends within
them. -/
theorem push_within (st : Array UInt64) (sp lo hi : UInt64) (n : Nat) (hsp : sp < 64)
    (hst : ∀ k < sp.toNat, st[2 * k + 1]!.toNat ≤ n) (hhi : hi.toNat ≤ n) :
    ∀ k < (sp + 1).toNat,
      ((st.set! (2 * sp).toNat lo).set! (2 * sp + 1).toNat hi)[2 * k + 1]!.toNat ≤ n := by
  have h64 := UInt64.lt_iff_toNat_lt.mp hsp
  simp only [UInt64.reduceToNat] at h64
  have h2 : (2 * sp).toNat = 2 * sp.toNat := by
    simp only [UInt64.toNat_mul, UInt64.reduceToNat]; omega
  have h21 : (2 * sp + 1).toNat = 2 * sp.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]; omega
  have hs1 : (sp + 1).toNat = sp.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  intro k hk
  rw [hs1] at hk
  rw [h2, h21]
  by_cases hks : k = sp.toNat
  · subst hks
    exact (get_set_le _ _ _).trans hhi
  · rw [get_set_ne _ _ _ _ (by omega), get_set_ne _ _ _ _ (by omega)]
    exact hst k (by omega)

/-- A pop takes a subfile that ends within `n` words and keeps the others within them. -/
theorem pop_within (st : Array UInt64) (sp : UInt64) (n : Nat) (h : 0 < sp ∧ sp ≤ 64)
    (hst : ∀ k < sp.toNat, st[2 * k + 1]!.toNat ≤ n) :
    st[(2 * (sp - 1) + 1).toNat]!.toNat ≤ n ∧
      ∀ k < (sp - 1).toNat, st[2 * k + 1]!.toNat ≤ n := by
  have h0 := UInt64.lt_iff_toNat_lt.mp h.1
  have h64 := UInt64.le_iff_toNat_le.mp h.2
  simp only [UInt64.reduceToNat] at h0 h64
  have hs : (sp - 1).toNat = sp.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  have h21 : (2 * (sp - 1) + 1).toNat = 2 * (sp.toNat - 1) + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, hs, UInt64.reduceToNat]; omega
  rw [h21, hs]
  exact ⟨hst _ (by omega), fun k hk => hst k (by omega)⟩

/-- Steps Q2 to Q8 return a permutation of the array when the current subfile and every subfile on
the stack end within it. -/
theorem stages_perm (l e sp : UInt64) (st a : Array UInt64) :
    e.toNat ≤ a.size → (∀ k < sp.toNat, st[2 * k + 1]!.toNat ≤ a.size) →
      (stages l e sp st a).size = a.size ∧ (stages l e sp st a).toList.Perm a.toList := by
  fun_induction stages l e sp st a with
  | case1 l e sp st a hc r hr _ ih =>
    intro he hst
    have hp : l.toNat ≤ r.1.toNat ∧ r.1.toNat < e.toNat ∧ r.2.size = a.size ∧
        r.2.toList.Perm a.toList := part_within l e a hc.1 he
    have h := ih (by omega) (push_within st sp (r.1 + 1) e r.2.size hr.2.2
      (by rw [hp.2.2.1]; exact hst) (by rw [hp.2.2.1]; exact he))
    exact ⟨h.1.trans hp.2.2.1, h.2.trans hp.2.2.2⟩
  | case2 l e sp st a hc r hr _ ih =>
    intro he hst
    have hp : l.toNat ≤ r.1.toNat ∧ r.1.toNat < e.toNat ∧ r.2.size = a.size ∧
        r.2.toList.Perm a.toList := part_within l e a hc.1 he
    have h := ih (by omega) (push_within st sp l r.1 r.2.size hr.2.2
      (by rw [hp.2.2.1]; exact hst) (by omega))
    exact ⟨h.1.trans hp.2.2.1, h.2.trans hp.2.2.2⟩
  | case3 l e sp st a hc r _ _ ih =>
    intro he hst
    have hp : l.toNat ≤ r.1.toNat ∧ r.1.toNat < e.toNat ∧ r.2.size = a.size ∧
        r.2.toList.Perm a.toList := part_within l e a hc.1 he
    have h := ih (by omega) (by rw [hp.2.2.1]; exact hst)
    exact ⟨h.1.trans hp.2.2.1, h.2.trans hp.2.2.2⟩
  | case4 l e sp st a hc r _ _ ih =>
    intro he hst
    have hp : l.toNat ≤ r.1.toNat ∧ r.1.toNat < e.toNat ∧ r.2.size = a.size ∧
        r.2.toList.Perm a.toList := part_within l e a hc.1 he
    have h := ih (by omega) (by rw [hp.2.2.1]; exact hst)
    exact ⟨h.1.trans hp.2.2.1, h.2.trans hp.2.2.2⟩
  | case5 l e sp st a _ hpop ih =>
    intro _ hst
    have hw := pop_within st sp a.size hpop hst
    exact ih hw.1 hw.2
  | case6 =>
    intro _ _
    exact ⟨rfl, List.Perm.refl _⟩

/-- Quicksort computes the specification on every array that memory can hold. -/
theorem quicksort_eq (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    quicksort xs = expected xs := by
  have hN : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  have h := stages_perm 0 xs.size.toUInt64 0 (LeanExe.build 128 fun _ => 0) xs (by rw [hN])
    (fun k hk => by simp at hk)
  obtain ⟨hs, hp⟩ := Library.Sorting.StraightInsertion.straightInsertion_sorted_perm
    (stages 0 xs.size.toUInt64 0 (LeanExe.build 128 fun _ => 0) xs) (by rw [h.1]; exact hsize)
  show straightInsertion (stages 0 xs.size.toUInt64 0 (LeanExe.build 128 fun _ => 0) xs) =
    expected xs
  unfold expected
  rw [← Library.Sorting.eq_mergeSort_of_sorted_perm hs (hp.trans h.2), Array.toArray_toList]

end Library.Sorting.Quicksort
