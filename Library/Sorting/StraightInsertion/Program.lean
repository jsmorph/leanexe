import LeanExe.Dialect.Loop

/-! Straight insertion, Algorithm S of TAOCP §5.2.1, on an array of words, in place, with indices
from 0.  For `j` from 1 to `n - 1` the words `xs[0, j)` are in order, and the program inserts the
word `v` at `j` among them: while the word to the left of the vacant position `i` exceeds `v`, that
word moves one place right and `i` decreases, and then `v` goes into position `i`.  A word equal to
`v` stays to its left. -/

namespace Library.Sorting.StraightInsertion

/-- Steps S3 to S5 with the vacant position `i`: while `0 < i` and `v < xs[i - 1]`, the word at
`i - 1` moves to `i` and `i` decreases, and then `v` goes into position `i`.  Knuth's step S4 tests
`i > 0` after it decreases `i`, and the program tests `0 < i` before it reads `xs[i - 1]`, so no
index wraps. -/
def shift (v i : UInt64) (xs : Array UInt64) : Array UInt64 :=
  if 0 < i then
    if v < xs[(i - 1).toNat]! then shift v (i - 1) (xs.set! i.toNat xs[(i - 1).toNat]!)
    else xs.set! i.toNat v
  else xs.set! i.toNat v
termination_by i.toNat
decreasing_by
  have h : 0 < i := by assumption
  have := UInt64.toNat_lt i
  simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h
  simp only [UInt64.toNat_sub, UInt64.reduceToNat]
  omega

/-- Algorithm S with `n = xs.size`: arrays of 0 and 1 elements return unchanged, and otherwise the
loop performs steps S2 to S5 for `j` from 1 to `n - 1`, with `v` the word at `j`.  The program reads
the size once, before the loop takes the array. -/
def straightInsertion (xs : Array UInt64) : Array UInt64 :=
  let n := xs.size.toUInt64
  if n ≤ 1 then xs
  else LeanExe.loop (n - 1) xs fun k acc => shift acc[(k + 1).toNat]! (k + 1) acc

end Library.Sorting.StraightInsertion
