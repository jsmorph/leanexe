/-! Binary search, Algorithm B of TAOCP §6.2.1, in the form that returns the least index whose
element is at least the key.  Indices start at 0, and the half-open range `[lo, hi)` holds Knuth's
records `l` through `u` at the indices `l - 1` through `u - 1`.  Knuth assumes distinct keys in
increasing order, and his step B3 compares three ways and stops at an equal key.  The program
assumes nondecreasing order, compares two ways, and stops only when the range is empty, so it
returns the first index of a run of equal words and the insertion point of a missing key.  The
midpoint `lo + (hi - lo) / 2` replaces Knuth's `⌊(l + u)/2⌋`, whose sum `l + u` can exceed a
word.  On a range of even length it is the upper of the two middle indices, where Knuth's is the
lower. -/

namespace Library.Arrays.BinarySearch

/-- Steps B2 to B5 on `[lo, hi)`, for `lo ≤ hi ≤ xs.size` and an array sorted in nondecreasing
order on that range: the least index of `[lo, hi)` whose element is at least `key`, or `hi` when
there is none.  Each step keeps the answer between `lo` and `hi`.  When the element at the midpoint
is less than `key`, `lo` moves past the midpoint, as in step B5.  Otherwise `hi` moves to the
midpoint, which stays a candidate, where Knuth's step B4 sets `u ← i - 1`.  The midpoint lies in
`[lo, hi)`, so its computation does not wrap.  The program writes the midpoint out in each place
rather than binding it with `let`, because the compiler's termination proof of the loop matches the
branch conditions syntactically. -/
def search (xs : Array UInt64) (key lo hi : UInt64) : UInt64 :=
  if lo < hi then
    if xs[(lo + (hi - lo) / 2).toNat]! < key then search xs key (lo + (hi - lo) / 2 + 1) hi
    else search xs key lo (lo + (hi - lo) / 2)
  else lo
termination_by (hi - lo).toNat
decreasing_by
  all_goals
    have hlt : lo < hi := by assumption
    have := UInt64.toNat_lt lo
    have := UInt64.toNat_lt hi
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_div,
      UInt64.reduceToNat] at hlt ⊢
    omega

/-- Step B1: on an array sorted in nondecreasing order, the least index whose element is at least
`key`, or the array's length when no element is, by `search` on `[0, xs.size)`.  The specification
does not fix the result on an unsorted array. -/
def lowerBound (xs : Array UInt64) (key : UInt64) : UInt64 :=
  search xs key 0 xs.size.toUInt64

end Library.Arrays.BinarySearch
