/-! The specification of binary search.  Indices start at 0.  For an array sorted in nondecreasing
order, the elements less than the key form a prefix, so the least index whose element is at least
the key, or the array's length when no element is, equals the number of elements less than the key,
which `expected` states.  The search assumes the order, and `Sorted` states it: on an unsorted
array the search's result is not specified.  The specification fixes the result and not the
method, so the program text alone shows that the module searches by halving.  The count fits in a
word for every array of fewer than `2^64` elements, which every array in memory is. -/

namespace Library.Arrays.BinarySearch

/-- The array is sorted in nondecreasing order. -/
def Sorted (xs : Array UInt64) : Prop :=
  ∀ i j, i ≤ j → j < xs.size → xs[i]! ≤ xs[j]!

/-- The number of elements of the array less than the key, as a word. -/
def expected (x : Array UInt64 × UInt64) : UInt64 :=
  UInt64.ofNat (x.1.toList.countP fun y => y < x.2)

end Library.Arrays.BinarySearch
