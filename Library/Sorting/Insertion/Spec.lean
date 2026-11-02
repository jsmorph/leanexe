/-! The specification of `sortInsert`: the array's elements in nondecreasing order, as Lean's
`List.mergeSort` arranges them, with words compared as unsigned numbers.  Exactly one list holds the
same words with the same repetitions in nondecreasing order, so the specification names the result
and not a method.  The theorems concern arrays of fewer than `2^64` elements, which every array in
memory is. -/

namespace Library.Sorting.Insertion

def expected (xs : Array UInt64) : Array UInt64 :=
  (xs.toList.mergeSort fun a b => a ≤ b).toArray

end Library.Sorting.Insertion
