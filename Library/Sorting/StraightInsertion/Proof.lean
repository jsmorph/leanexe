import Library.Sorting.StraightInsertion.Program
import Library.Sorting.StraightInsertion.Spec
import Library.Sorting.Sorted
import LeanExe.Dialect.Lemmas
import Mathlib.Data.List.Sort

/-! The proof that straight insertion returns the array's elements in nondecreasing order.  One
insertion is a statement about lists: when the words `xs[0, i)` are in order, `shift v i xs` puts
`xs[0, i)` with `v` inserted after every word at most `v`, which is `orderedInsert (· < ·) v`, into
positions `0` to `i` and leaves the words after `i` unchanged (`shift_toList`).  Each pass of the
loop keeps the first `j + 1` words in order, a permutation of the first `j + 1` words of the input,
and the rest of the input unchanged (`straightInsertion_sorted_perm`).  A sorted permutation is
unique, so the result equals `expected`. -/

namespace Library.Sorting.StraightInsertion

open LeanExe.Dialect

/-! ### Insertion into a list -/

theorem orderedInsert_append_of_lt {v y : UInt64} (h : v < y) (l : List UInt64) :
    (l ++ [y]).orderedInsert (· < ·) v = l.orderedInsert (· < ·) v ++ [y] := by
  induction l with
  | nil => simp [h]
  | cons b l ih => by_cases hb : v < b <;> simp [hb, ih]

theorem orderedInsert_of_forall_not_lt {v : UInt64} :
    ∀ l : List UInt64, (∀ b ∈ l, ¬ v < b) → l.orderedInsert (· < ·) v = l ++ [v]
  | [], _ => rfl
  | b :: l, h => by
    have hb := h b (by simp)
    simp only [List.orderedInsert_cons, hb, ite_false, List.cons_append]
    rw [orderedInsert_of_forall_not_lt l fun c hc => h c (by simp [hc])]

theorem pairwise_orderedInsert (v : UInt64) :
    ∀ l : List UInt64, l.Pairwise (· ≤ ·) → (l.orderedInsert (· < ·) v).Pairwise (· ≤ ·)
  | [], _ => by simp
  | b :: l, h => by
    rw [List.pairwise_cons] at h
    by_cases hb : v < b
    · simp only [List.orderedInsert_cons, hb, ite_true]
      refine List.Pairwise.cons (fun c hc => ?_) (List.Pairwise.cons h.1 h.2)
      rw [UInt64.lt_iff_toNat_lt] at hb
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [UInt64.le_iff_toNat_le]; omega
      · have := UInt64.le_iff_toNat_le.mp (h.1 c hc)
        rw [UInt64.le_iff_toNat_le]; omega
    · simp only [List.orderedInsert_cons, hb, ite_false]
      refine List.Pairwise.cons (fun c hc => ?_) (pairwise_orderedInsert v l h.2)
      rw [List.mem_orderedInsert] at hc
      rcases hc with rfl | hc
      · rw [UInt64.lt_iff_toNat_lt] at hb
        rw [UInt64.le_iff_toNat_le]; omega
      · exact h.1 c hc

/-! ### One insertion -/

theorem take_set_succ (L : List UInt64) (m : Nat) (y : UInt64) (h : m + 1 < L.length) :
    (L.set (m + 1) y).take m = L.take m ∧
      (L.set (m + 1) y).drop (m + 1) = y :: L.drop (m + 2) := by
  rw [List.set_eq_take_append_cons_drop, ite_eq_left h]
  have hlen : (L.take (m + 1)).length = m + 1 := by simp; omega
  constructor
  · rw [List.take_append, hlen, show m - (m + 1) = 0 by omega, List.take_zero, List.append_nil,
      List.take_take, Nat.min_eq_left (by omega)]
  · rw [List.drop_append, hlen, List.drop_eq_nil_of_le (by rw [hlen]), Nat.sub_self,
      List.drop_zero, List.nil_append]

/-- One insertion: when `xs[0, i)` is in order, `shift v i xs` holds `xs[0, i)` with `v` inserted
after every word at most `v` in positions `0` to `i`, and the words of `xs` after `i`. -/
theorem shift_toList (v : UInt64) :
    ∀ (n : Nat) (i : UInt64) (xs : Array UInt64), i.toNat = n → i.toNat < xs.size →
      (xs.toList.take i.toNat).Pairwise (· ≤ ·) →
      (shift v i xs).toList =
        (xs.toList.take i.toNat).orderedInsert (· < ·) v ++ xs.toList.drop (i.toNat + 1) := by
  intro n
  induction n with
  | zero =>
    intro i xs hi hlt _
    have h0 : ¬ 0 < i := by rw [UInt64.lt_iff_toNat_lt]; simp [hi]
    rw [shift, ite_eq_right h0, Array.toList_set!, hi, List.set_eq_take_append_cons_drop,
      ite_eq_left (by simpa [hi] using hlt)]
    simp
  | succ m ih =>
    intro i xs hi hlt hsorted
    have h0 : 0 < i := by rw [UInt64.lt_iff_toNat_lt]; simp [hi]
    have him : (i - 1).toNat = m := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp [hi]
    have hm : m < xs.toList.length := by simp; omega
    have hget : xs[(i - 1).toNat]! = xs.toList[m] := by
      rw [him, getElem!_pos xs m (by simpa using hm), Array.getElem_toList]
    have htake : xs.toList.take (m + 1) = xs.toList.take m ++ [xs.toList[m]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some]
    rw [hi] at hsorted ⊢
    rw [shift, ite_eq_left h0, hget, htake]
    by_cases hlt' : v < xs.toList[m]
    · rw [ite_eq_left hlt']
      have hset := take_set_succ xs.toList m xs.toList[m] (by simpa [hi] using hlt)
      have hsize : (i - 1).toNat < (xs.set! i.toNat xs.toList[m]).size := by
        simp only [Array.size_set!]; omega
      have hs' : ((xs.set! i.toNat xs.toList[m]).toList.take (i - 1).toNat).Pairwise (· ≤ ·) := by
        rw [Array.toList_set!, hi, him, hset.1]
        rw [htake] at hsorted
        exact (List.pairwise_append.mp hsorted).1
      rw [ih (i - 1) _ him hsize hs', Array.toList_set!, hi, him, hset.1, hset.2,
        orderedInsert_append_of_lt hlt']
      simp
    · rw [ite_eq_right hlt', Array.toList_set!, hi, List.set_eq_take_append_cons_drop,
        ite_eq_left (by simpa [hi] using hlt), htake]
      rw [htake] at hsorted
      have hall : ∀ b ∈ xs.toList.take m ++ [xs.toList[m]], ¬ v < b := by
        intro b hb
        rw [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · have := UInt64.le_iff_toNat_le.mp
            ((List.pairwise_append.mp hsorted).2.2 b hb _ (List.mem_singleton_self _))
          rw [UInt64.lt_iff_toNat_lt] at hlt' ⊢; omega
        · exact hlt'
      rw [orderedInsert_of_forall_not_lt _ hall]
      simp

/-! ### Sorting -/

/-- `straightInsertion` returns a permutation of its input in nondecreasing order. -/
theorem straightInsertion_sorted_perm (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    (straightInsertion xs).toList.Pairwise (· ≤ ·) ∧
      (straightInsertion xs).toList.Perm xs.toList := by
  have hN : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  simp only [straightInsertion]
  by_cases h1 : xs.size.toUInt64 ≤ 1
  · rw [ite_eq_left h1]
    have : xs.toList.length ≤ 1 := by
      have := UInt64.le_iff_toNat_le.mp h1; simp [hN] at this; simpa using this
    refine ⟨?_, List.Perm.refl _⟩
    match hl : xs.toList, this with
    | [], _ => exact List.Pairwise.nil
    | [_], _ => exact List.pairwise_singleton _ _
  · rw [ite_eq_right h1]
    have hN2 : 2 ≤ xs.size := by
      have : ¬ xs.size.toUInt64.toNat ≤ 1 := fun h =>
        h1 (UInt64.le_iff_toNat_le.mpr (by simpa using h))
      omega
    have hcount : (xs.size.toUInt64 - 1).toNat = xs.size - 1 := by
      simp only [UInt64.toNat_sub, hN, UInt64.reduceToNat]; omega
    have h := loop_induction (n := xs.size.toUInt64 - 1) (init := xs)
      (f := fun k acc => shift acc[(k + 1).toNat]! (k + 1) acc)
      (P := fun k acc => acc.size = xs.size ∧
        (acc.toList.take (k + 1)).Pairwise (· ≤ ·) ∧
        (acc.toList.take (k + 1)).Perm (xs.toList.take (k + 1)) ∧
        acc.toList.drop (k + 1) = xs.toList.drop (k + 1))
      ⟨rfl, by
        rw [List.take_add_one, List.take_zero, List.nil_append]
        cases xs.toList[0]? <;> simp, List.Perm.refl _, rfl⟩
      (by
        intro k acc hk ⟨hs, hp, hperm, hdrop⟩
        rw [hcount] at hk
        have hj : (UInt64.ofNat k + 1).toNat = k + 1 := by
          simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]; omega
        have hlen : k + 1 < acc.toList.length := by simp; omega
        have hv : acc[(UInt64.ofNat k + 1).toNat]! = xs.toList[k + 1] := by
          rw [hj, getElem!_pos acc (k + 1) (by simpa using hlen), ← Array.getElem_toList]
          have := congrArg (·[0]?) hdrop
          simp only [List.getElem?_drop, Nat.add_zero] at this
          rw [List.getElem?_eq_getElem hlen, List.getElem?_eq_getElem (by simp; omega)] at this
          exact Option.some.inj this
        have hst := shift_toList (xs.toList[k + 1]) (k + 1) (UInt64.ofNat k + 1) acc hj
          (by rw [hj]; simpa using hlen) (by rw [hj]; exact hp)
        rw [hv, hst, hj]
        have hilen : ((acc.toList.take (k + 1)).orderedInsert (· < ·) xs.toList[k + 1]).length =
            k + 1 + 1 := by
          rw [List.orderedInsert_length, List.length_take, Nat.min_eq_left (by omega)]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [← Array.length_toList, hst, hj, List.length_append, hilen, List.length_drop,
            Array.length_toList, hs]
          omega
        · rw [List.take_append_of_le_length (by rw [hilen]), List.take_of_length_le (by rw [hilen])]
          exact pairwise_orderedInsert _ _ hp
        · rw [List.take_append_of_le_length (by rw [hilen]), List.take_of_length_le (by rw [hilen])]
          have hx : xs.toList.take (k + 1 + 1) = xs.toList.take (k + 1) ++ [xs.toList[k + 1]] := by
            rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega), Option.toList_some]
          rw [hx]
          exact (List.perm_orderedInsert _ _ _).trans
            ((hperm.cons _).trans (List.perm_append_singleton _ _).symm)
        · rw [List.drop_append, hilen, List.drop_eq_nil_of_le (le_of_eq hilen), List.nil_append,
            Nat.sub_self, List.drop_zero]
          have h2 : ∀ l : List UInt64, l.drop (k + 1 + 1) = (l.drop (k + 1)).drop 1 := fun l => by
            rw [List.drop_drop]
          rw [h2 acc.toList, h2 xs.toList, hdrop])
    rw [hcount] at h
    obtain ⟨hs, hp, hperm, -⟩ := h
    have hfull : xs.size - 1 + 1 = xs.size := by omega
    rw [hfull] at hp hperm
    generalize LeanExe.loop (xs.size.toUInt64 - 1) xs
      (fun k acc => shift acc[(k + 1).toNat]! (k + 1) acc) = r at hs hp hperm ⊢
    rw [List.take_of_length_le (l := r.toList) (i := xs.size) (by simp [hs])] at hp hperm
    rw [List.take_of_length_le (l := xs.toList) (i := xs.size) (by simp)] at hperm
    exact ⟨hp, hperm⟩

/-- Straight insertion computes the specification on every array that memory can hold. -/
theorem straightInsertion_eq (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    straightInsertion xs = expected xs := by
  obtain ⟨hs, hp⟩ := straightInsertion_sorted_perm xs hsize
  unfold expected
  rw [← Library.Sorting.eq_mergeSort_of_sorted_perm hs hp, Array.toArray_toList]

end Library.Sorting.StraightInsertion
