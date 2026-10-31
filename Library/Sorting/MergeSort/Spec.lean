/-! The specification of sorting: the array's elements in nondecreasing order, as Lean's
`List.mergeSort` arranges them.  Words compare as unsigned numbers.  Exactly one list holds the same
words with the same repetitions in nondecreasing order, so the specification names the result and
not a method, and stability has no effect on words.  The specification cannot state that the
program merges runs bottom-up, writing each pass into a new array, which the program text shows.
The program merges adjacent runs from left to right, as the request describes, where Knuth's
Algorithm S takes its runs from the two ends of the area; both forms give the same result.
The theorems concern arrays of fewer than `2^64` elements, which every array in memory is. -/

namespace Library.Sorting.MergeSort

def expected (xs : Array UInt64) : Array UInt64 :=
  (xs.toList.mergeSort fun a b => a ≤ b).toArray

end Library.Sorting.MergeSort
