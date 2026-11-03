import LeanExe.Dialect.Loop
import Library.Sorting.StraightInsertion.Program

/-! Shellsort, Algorithm D of TAOCP §5.2.1, on an array of words, in place, with indices from 0.
The increments are Knuth's: `h_1 = 1` and `h_{s+1} = 3h_s + 1`, from `h_t`, the first increment with
`h_{t+2} ≥ N`, down to 1, so an array of fewer than 14 words has only the increment 1.  For each
increment `h` above 1, `pass` inserts the word at each position `j` from `h` to `N - 1` among the
words `h`, `2h`, … places before it, which are in order.  The pass with increment 1 is Algorithm S,
so the program ends with `straightInsertion`. -/

namespace Library.Sorting.Shellsort

open Library.Sorting.StraightInsertion (straightInsertion)

/-- Steps D4 to D6 with the increment `h` and the vacant position `i`: while `h ≤ i` and
`v < xs[i - h]`, the word at `i - h` moves to `i` and `i` decreases by `h`, and then `v` is written
into position `i`.  The program tests `h ≤ i` before it reads `xs[i - h]`, so no index wraps, and an
increment of 0 stores `v` at once. -/
def insertBy (v h i : UInt64) (xs : Array UInt64) : Array UInt64 :=
  if 0 < h then
    if h ≤ i then
      if v < xs[(i - h).toNat]! then insertBy v h (i - h) (xs.set! i.toNat xs[(i - h).toNat]!)
      else xs.set! i.toNat v
    else xs.set! i.toNat v
  else xs.set! i.toNat v
termination_by i.toNat
decreasing_by
  have h0 : 0 < h := by assumption
  have h1 : h ≤ i := by assumption
  simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h0
  rw [UInt64.le_iff_toNat_le] at h1
  simp only [UInt64.toNat_sub]
  have := UInt64.toNat_lt i
  omega

/-- Steps D2 to D6 for the increment `h`: for `j` from `h` to `n - 1`, the word at `j` goes among
the words `h`, `2h`, … places before it.  The program reads the size once, before the loop takes
the array. -/
def pass (h : UInt64) (xs : Array UInt64) : Array UInt64 :=
  let n := xs.size.toUInt64
  if h < n then LeanExe.loop (n - h) xs fun k acc => insertBy acc[(h + k).toNat]! h (h + k) acc
  else xs

/-- Step D1 for the increments `h`, `(h - 1) / 3`, and so on, while they exceed 1. -/
def passes (h : UInt64) (xs : Array UInt64) : Array UInt64 :=
  if 1 < h then passes ((h - 1) / 3) (pass h xs) else xs
termination_by h.toNat
decreasing_by
  have h1 : 1 < h := by assumption
  simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h1
  simp only [UInt64.toNat_div, UInt64.toNat_sub, UInt64.reduceToNat]
  have := UInt64.toNat_lt h
  omega

/-- Knuth's first increment for `n` words, from `h`: the next increment while `h_{s+2} = 9h + 4`
is below `n`.  For `4 < n` the program tests `9h + 4 < n` as `h ≤ (n - 5) / 9`, which computes
neither `9h + 4` nor a difference below 0, so no word wraps, and for `n ≤ 4` it returns `h`. -/
def firstIncrement (n h : UInt64) : UInt64 :=
  if 4 < n then (if h ≤ (n - 5) / 9 then firstIncrement n (3 * h + 1) else h) else h
termination_by (n - h).toNat
decreasing_by
  have h4 : 4 < n := by assumption
  have hh : h ≤ (n - 5) / 9 := by assumption
  have hn := UInt64.lt_iff_toNat_lt.mp h4
  simp only [UInt64.reduceToNat] at hn
  have hlt := UInt64.toNat_lt n
  have h5 : (n - 5).toNat = n.toNat - 5 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
  have hb : h.toNat ≤ (n.toNat - 5) / 9 := by
    have := UInt64.le_iff_toNat_le.mp hh
    simpa only [UInt64.toNat_div, h5, UInt64.reduceToNat] using this
  have h3 : (3 * h + 1).toNat = 3 * h.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
    omega
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [h3]; omega)),
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), h3]
  omega

/-- Algorithm D: the passes with the increments `h_t` to `h_2`, then straight insertion, the pass
with the increment 1. -/
def shellsort (xs : Array UInt64) : Array UInt64 :=
  straightInsertion (passes (firstIncrement xs.size.toUInt64 1) xs)

end Library.Sorting.Shellsort
