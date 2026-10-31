import LeanExe.Dialect.Build

/-! Straight two-way merge sort, TAOCP §5.2.4, bottom-up.  A pass of width `w` merges each pair of
adjacent runs `[lo, lo + w)` and `[lo + w, lo + 2w)` of the array, cut at its length `n`, into a
new array, and the passes double `w` from 1 until a run covers the array.  The merge takes the
word of the first run when it is at most the word of the second, as `List.merge` does.  Run ends
are computed as `lo + min w (n - lo)`, which never exceeds `n` and so never wraps. -/

namespace Library.Sorting.MergeSort

/-- The end of the run of width `w` that starts at `lo` in `[0, n)`. -/
def runEnd (lo w n : UInt64) : UInt64 := lo + min w (n - lo)

theorem runEnd_toNat {lo w n : UInt64} (h : lo ≤ n) :
    (runEnd lo w n).toNat = lo.toNat + min w.toNat (n.toNat - lo.toNat) := by
  have hn := UInt64.toNat_lt n
  have hl := UInt64.le_iff_toNat_le.mp h
  have hs : (n - lo).toNat = n.toNat - lo.toNat := UInt64.toNat_sub_of_le _ _ h
  unfold runEnd
  rw [Std.min_eq_ite]
  split
  · rename_i hw
    have hw' := UInt64.le_iff_toNat_le.mp hw
    rw [hs] at hw'
    rw [UInt64.toNat_add, Nat.min_eq_left hw']
    omega
  · rename_i hw
    have hw' : ¬ w.toNat ≤ n.toNat - lo.toNat := fun h' =>
      hw (UInt64.le_iff_toNat_le.mpr (by rw [hs]; exact h'))
    rw [UInt64.toNat_add, hs, Nat.min_eq_right (by omega)]
    omega

/-- Merge the runs `src[i, iEnd)` and `src[j, jEnd)` into `out` from position `k`, taking the word
of the first run while it is at most the word of the second. -/
def merge (src : Array UInt64) (k i iEnd j jEnd : UInt64) (out : Array UInt64) : Array UInt64 :=
  if i < iEnd ∧ (jEnd ≤ j ∨ src[i.toNat]! ≤ src[j.toNat]!) then
    merge src (k + 1) (i + 1) iEnd j jEnd (out.set! k.toNat src[i.toNat]!)
  else if j < jEnd then
    merge src (k + 1) i iEnd (j + 1) jEnd (out.set! k.toNat src[j.toNat]!)
  else out
termination_by (iEnd - i).toNat + (jEnd - j).toNat
decreasing_by
  · have h : i < iEnd ∧ (jEnd ≤ j ∨ src[i.toNat]! ≤ src[j.toNat]!) := by assumption
    have := UInt64.lt_iff_toNat_lt.mp h.1
    have := UInt64.toNat_lt iEnd
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  · have h : j < jEnd := by assumption
    have := UInt64.lt_iff_toNat_lt.mp h
    have := UInt64.toNat_lt jEnd
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
    omega

/-- One pass of width `w` from position `lo`: merge the runs `[lo, mid)` and `[mid, hi)` of `src`,
with `mid` and `hi` the ends of runs of width `w`, into `out`, and continue from `hi`. -/
def pass (src : Array UInt64) (w n lo : UInt64) (out : Array UInt64) : Array UInt64 :=
  if 0 < w ∧ lo < n then
    pass src w n (runEnd (runEnd lo w n) w n)
      (merge src lo lo (runEnd lo w n) (runEnd lo w n) (runEnd (runEnd lo w n) w n) out)
  else out
termination_by (n - lo).toNat
decreasing_by
  have h : 0 < w ∧ lo < n := by assumption
  have hw := UInt64.lt_iff_toNat_lt.mp h.1
  have hl := UInt64.lt_iff_toNat_lt.mp h.2
  have h1 := runEnd_toNat (w := w) (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt hl))
  have h2 := runEnd_toNat (lo := runEnd lo w n) (w := w) (n := n)
    (UInt64.le_iff_toNat_le.mpr (by simp only [UInt64.reduceToNat] at hw; omega))
  simp only [UInt64.reduceToNat] at hw
  simp only [UInt64.toNat_sub]
  have := UInt64.toNat_lt n
  omega

/-- The passes of widths `w`, `2w`, and so on, while a run is shorter than `n`.  The width doubles
while `2w < n` and becomes `n` otherwise, so it never wraps. -/
def sortLoop (w n : UInt64) (xs : Array UInt64) : Array UInt64 :=
  if 0 < w ∧ w < n then
    sortLoop (if w < n - w then w + w else n) n (pass xs w n 0 (LeanExe.build n fun _ => 0))
  else xs
termination_by (n - w).toNat
decreasing_by
  have h : 0 < w ∧ w < n := by assumption
  have hw := UInt64.lt_iff_toNat_lt.mp h.1
  have hl := UInt64.lt_iff_toNat_lt.mp h.2
  have := UInt64.toNat_lt n
  simp only [UInt64.reduceToNat] at hw
  split
  · rename_i h2
    have := UInt64.lt_iff_toNat_lt.mp h2
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat] at *
    omega
  · simp only [UInt64.toNat_sub, UInt64.reduceToNat]
    omega

/-- The array in nondecreasing order. -/
def mergeSort (xs : Array UInt64) : Array UInt64 :=
  sortLoop 1 xs.size.toUInt64 xs

end Library.Sorting.MergeSort
