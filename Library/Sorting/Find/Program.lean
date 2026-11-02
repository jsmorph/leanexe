import Library.Sorting.Quicksort.Program

/-! Hoare's FIND on an array of words, in place, with indices from 0 and subfiles written as
half-open ranges `[l, e)`.  `find` partitions the subfile that holds position `k` around its first
word with quicksort's `part`, steps Q3 to Q6 of TAOCP §5.2.2, and continues with the part that holds
`k`, until the partitioning word's final position is `k` or the subfile has at most one word.  The
word at `k` is then at least every word before it and at most every word after it. -/

namespace Library.Sorting.Find

open Library.Sorting.Quicksort (part part_fst span span_eq succ_toNat)

/-- FIND on the subfile `[l, e)`: a subfile of two or more words is partitioned around its first
word, and the loop continues with the part before the word's final position `j` when `k < j`, with
the part after it when `j < k`, and ends when `j = k`. -/
def find (k l e : UInt64) (a : Array UInt64) : Array UInt64 :=
  if l < e ∧ 1 < e - l then
    let r := part a[l.toNat]! l e l e a
    if k < r.1 then find k l r.1 r.2
    else if r.1 < k then find k (r.1 + 1) e r.2
    else r.2
  else a
termination_by span l e
decreasing_by
  all_goals try simp only [r] at *
  · obtain ⟨hc, -⟩ : l < e ∧ 1 < e - l := by assumption
    have hj := part_fst a[l.toNat]! l e a l e (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)) hc
    have he := UInt64.lt_iff_toNat_lt.mp hc
    rw [span_eq (UInt64.le_iff_toNat_le.mpr hj.1), span_eq (UInt64.le_iff_toNat_le.mpr (by omega))]
    omega
  · obtain ⟨hc, -⟩ : l < e ∧ 1 < e - l := by assumption
    have hj := part_fst a[l.toNat]! l e a l e (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)) hc
    have he := UInt64.lt_iff_toNat_lt.mp hc
    have hj1 := succ_toNat (UInt64.lt_iff_toNat_lt.mpr hj.2)
    rw [span_eq (UInt64.le_iff_toNat_le.mpr (by omega)),
      span_eq (UInt64.le_iff_toNat_le.mpr (by omega)), hj1]
    omega

/-- The word of rank `k` of `xs`: when `k` is a position of the array, FIND over the whole array
and then the word at `k`, and 0 otherwise. -/
def select (xs : Array UInt64) (k : UInt64) : UInt64 :=
  let n := xs.size.toUInt64
  if k < n then (find k 0 n xs)[k.toNat]! else 0

end Library.Sorting.Find
