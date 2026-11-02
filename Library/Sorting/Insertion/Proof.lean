import Library.Sorting.Insertion.Program
import Library.Sorting.Insertion.Spec
import Library.Sorting.Sorted
import LeanExe.Dialect.Lemmas

/-! The proof that `sortInsert` returns the array's elements in nondecreasing order.  The inner loop
counts the words of the accumulated array that are below the next word `v` (`count_eq`).  In a list
in nondecreasing order those words come first, so inserting `v` at their count keeps the order
(`insertIdx_countP_pairwise`).  The outer loop therefore keeps the accumulated array in order and a
permutation of the words read so far (`sortInsert_sorted_perm`), and a sorted permutation is
unique, so the result equals `expected`. -/

namespace Library.Sorting.Insertion

open LeanExe.Dialect

/-- Inserting `v` into a list in nondecreasing order at the count of its words below `v` keeps the
order. -/
theorem insertIdx_countP_pairwise (v : UInt64) :
    ∀ l : List UInt64, l.Pairwise (· ≤ ·) →
      (l.insertIdx (l.countP fun b => decide (b < v)) v).Pairwise (· ≤ ·)
  | [], _ => by simp
  | b :: l, h => by
    rw [List.pairwise_cons] at h
    by_cases hb : b < v
    · have hc : (b :: l).countP (fun x => decide (x < v)) =
          l.countP (fun x => decide (x < v)) + 1 := by
        rw [List.countP_cons]; simp [hb]
      rw [hc, List.insertIdx_succ_cons]
      refine List.Pairwise.cons (fun c hc => ?_) (insertIdx_countP_pairwise v l h.2)
      rw [List.mem_insertIdx List.countP_le_length] at hc
      rcases hc with rfl | hc
      · rw [UInt64.lt_iff_toNat_lt] at hb; rw [UInt64.le_iff_toNat_le]; omega
      · exact h.1 c hc
    · have h0 : l.countP (fun x => decide (x < v)) = 0 := by
        rw [List.countP_eq_zero]
        intro c hc
        have := UInt64.le_iff_toNat_le.mp (h.1 c hc)
        rw [UInt64.lt_iff_toNat_lt] at hb
        simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt]; omega
      have hc : (b :: l).countP (fun x => decide (x < v)) = 0 := by
        rw [List.countP_cons, h0]; simp [hb]
      rw [hc, List.insertIdx_zero]
      refine List.Pairwise.cons (fun c hc => ?_) (List.Pairwise.cons h.1 h.2)
      rw [UInt64.lt_iff_toNat_lt] at hb
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [UInt64.le_iff_toNat_le]; omega
      · have := UInt64.le_iff_toNat_le.mp (h.1 c hc)
        rw [UInt64.le_iff_toNat_le]; omega

/-- The inner loop counts the words of `acc` below `v`. -/
theorem count_eq (acc : Array UInt64) (v : UInt64) (hsize : acc.size < 2 ^ 64) :
    (LeanExe.loop acc.size.toUInt64 (0 : UInt64) fun j c =>
      if acc[j.toNat]! < v then c + 1 else c).toNat =
      acc.toList.countP fun b => decide (b < v) := by
  have hN : acc.size.toUInt64.toNat = acc.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  have h := loop_induction (n := acc.size.toUInt64) (init := (0 : UInt64))
    (f := fun j c => if acc[j.toNat]! < v then c + 1 else c)
    (P := fun k c => c.toNat = (acc.toList.take k).countP fun b => decide (b < v))
    (by simp)
    (by
      intro k c hk ih
      rw [hN] at hk
      have hkk : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
      have hlen : k < acc.toList.length := by simp; omega
      have hcle : c.toNat ≤ k := by
        rw [ih]; exact Nat.le_trans List.countP_le_length (by simp)
      have hget : acc[(UInt64.ofNat k).toNat]! = acc.toList[k] := by
        rw [hkk, getElem!_pos acc k (by simpa using hlen), Array.getElem_toList]
      rw [hget, List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some,
        List.countP_append, ← ih]
      by_cases hv : acc.toList[k] < v
      · rw [ite_eq_left hv]
        have h1 : [acc.toList[k]].countP (fun b => decide (b < v)) = 1 := by
          have hv' : acc[k] < v := by simpa using hv
          simp [hv']
        rw [h1]
        simp only [UInt64.toNat_add, UInt64.reduceToNat]
        omega
      · rw [ite_eq_right hv]
        have h1 : [acc.toList[k]].countP (fun b => decide (b < v)) = 0 := by
          have hv' : ¬ acc[k] < v := by simpa using hv
          simp [hv']
        rw [h1, Nat.add_zero])
  rw [hN, List.take_of_length_le (by simp)] at h
  exact h

/-- `sortInsert` returns a permutation of its input in nondecreasing order. -/
theorem sortInsert_sorted_perm (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    (sortInsert xs).toList.Pairwise (· ≤ ·) ∧ (sortInsert xs).toList.Perm xs.toList := by
  have hN : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  have hb : (LeanExe.build 0 fun _ => (0 : UInt64)).toList = [] :=
    List.eq_nil_of_length_eq_zero (by rw [Array.length_toList, build_size]; rfl)
  have h := loop_induction (n := xs.size.toUInt64) (init := LeanExe.build 0 fun _ => (0 : UInt64))
    (f := fun i acc =>
      let v := xs[i.toNat]!
      let k := LeanExe.loop acc.size.toUInt64 0 fun j c => if acc[j.toNat]! < v then c + 1 else c
      LeanExe.insertAt acc k v)
    (P := fun i acc => acc.size = i ∧ acc.toList.Pairwise (· ≤ ·) ∧
      acc.toList.Perm (xs.toList.take i))
    ⟨by rw [build_size]; rfl, by rw [hb]; exact List.Pairwise.nil, by rw [hb, List.take_zero]⟩
    (by
      intro i acc hi ⟨hs, hp, hperm⟩
      rw [hN] at hi
      have hii : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
      have hlen : i < xs.toList.length := by simp; omega
      have hv : xs[(UInt64.ofNat i).toNat]! = xs.toList[i] := by
        rw [hii, getElem!_pos xs i (by simpa using hlen), Array.getElem_toList]
      simp only
      rw [hv]
      have hk := count_eq acc xs.toList[i] (by omega)
      generalize LeanExe.loop acc.size.toUInt64 (0 : UInt64)
        (fun j c => if acc[j.toNat]! < xs.toList[i] then c + 1 else c) = k at hk
      have hkle : k.toNat ≤ acc.size := by
        rw [hk, ← Array.length_toList]; exact List.countP_le_length
      have hl : (LeanExe.insertAt acc k xs.toList[i]).toList =
          acc.toList.insertIdx k.toNat xs.toList[i] := by
        rw [LeanExe.insertAt, Array.insertIdxIfInBounds, dite_eq_left hkle, Array.toList_insertIdx]
      refine ⟨?_, ?_, ?_⟩
      · rw [← Array.length_toList, hl, List.length_insertIdx, if_pos (by simpa using hkle),
          Array.length_toList, hs]
      · rw [hl, hk]
        exact insertIdx_countP_pairwise _ _ hp
      · rw [hl, List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some]
        exact (List.perm_insertIdx _ _ (by simpa using hkle)).trans
          ((hperm.cons _).trans (List.perm_append_singleton _ _).symm))
  rw [hN] at h
  obtain ⟨-, hp, hperm⟩ := h
  rw [List.take_of_length_le (by simp)] at hperm
  exact ⟨hp, hperm⟩

/-- `sortInsert` computes the specification on every array that memory can hold. -/
theorem sortInsert_eq (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    sortInsert xs = expected xs := by
  obtain ⟨hs, hp⟩ := sortInsert_sorted_perm xs hsize
  unfold expected
  rw [← Library.Sorting.eq_mergeSort_of_sorted_perm hs hp, Array.toArray_toList]

end Library.Sorting.Insertion
