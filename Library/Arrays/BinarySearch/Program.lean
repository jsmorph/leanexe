namespace Library.Arrays.BinarySearch

/-- Algorithm B of TAOCP §6.2.1, in the form that returns the least index of `[lo, hi)` whose
element is at least `key`, or `hi` when there is none, for an array sorted on that range.  The
midpoint `lo + (hi - lo) / 2` lies in `[lo, hi)`, so its computation does not wrap.  The midpoint is
written out rather than bound with `let`, because the compiler's termination proof of the loop
matches the branch conditions syntactically. -/
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

/-- The least index of the array whose element is at least `key`, or the array's length. -/
def lowerBound (xs : Array UInt64) (key : UInt64) : UInt64 :=
  search xs key 0 xs.size.toUInt64

end Library.Arrays.BinarySearch
