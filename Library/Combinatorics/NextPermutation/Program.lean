import Library.Sorting.Heapsort.Program

/-! The next arrangement in lexicographic order, one step of Algorithm L of TAOCP §7.2.1.2, on an
array of words, with indices from 0.  Step L2 finds the last position `j` with `a[j] < a[j + 1]`,
so that the words after `j` are in nonincreasing order, and when there is none, the array is the
greatest arrangement.  Step L3 finds the last position `l` after `j` with
`a[j] < a[l]` and exchanges the words at `j` and `l`, and step L4 reverses the words after `j`,
which puts them in nondecreasing order.  For the greatest arrangement the program reverses the
whole array, which gives the least arrangement, and returns the flag 0. -/

namespace Library.Combinatorics.NextPermutation

open Library.Sorting.Heapsort (swap)

/-- Step L2 from position `i`, which stands for `j + 1`: the greatest `r` with `0 < r ≤ i` and
`a[r - 1] < a[r]`, or 0 when there is none. -/
def ascent (a : Array UInt64) (i : UInt64) : UInt64 :=
  if 0 < i then (if a[(i - 1).toNat]! < a[i.toNat]! then i else ascent a (i - 1)) else 0
termination_by i.toNat
decreasing_by
  have h0 : 0 < i := by assumption
  simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h0
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt i
  omega

/-- Step L3 from position `l` down to `lo + 1`: the last position after `lo` whose word exceeds
`v`, or `lo` when there is none. -/
def lastAbove (a : Array UInt64) (v lo l : UInt64) : UInt64 :=
  if lo < l then (if v < a[l.toNat]! then l else lastAbove a v lo (l - 1)) else lo
termination_by l.toNat
decreasing_by
  have h0 : lo < l := by assumption
  simp only [UInt64.lt_iff_toNat_lt] at h0
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt l
  omega

/-- The words of positions `lo` to `hi` in reverse order, for `hi` below the size: step L4, and
the reversal of the whole array at the greatest arrangement. -/
def reverseRange (a : Array UInt64) (lo hi : UInt64) : Array UInt64 :=
  if lo < hi then reverseRange (swap lo hi a) (lo + 1) (hi - 1) else a
termination_by hi.toNat + 1 - lo.toNat
decreasing_by
  have h0 : lo < hi := by assumption
  have h1 := UInt64.lt_iff_toNat_lt.mp h0
  have := UInt64.toNat_lt hi
  have e1 : (hi - 1).toNat = hi.toNat - 1 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
  have e2 : (lo + 1).toNat = lo.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]
    omega
  rw [e1, e2]
  omega

/-- The flag and the next arrangement of `a`. -/
def nextPerm (a : Array UInt64) : UInt64 × Array UInt64 :=
  let n := a.size.toUInt64
  if n ≤ 1 then (0, a)
  else
    let i := ascent a (n - 1)
    if i = 0 then (0, reverseRange a 0 (n - 1))
    else
      let l := lastAbove a a[(i - 1).toNat]! i (n - 1)
      (1, reverseRange (swap (i - 1) l a) i (n - 1))

end Library.Combinatorics.NextPermutation
