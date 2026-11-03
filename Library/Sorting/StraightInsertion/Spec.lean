/-! The specification of sorting: the array's elements in nondecreasing order, as Lean's
`List.mergeSort` arranges them.  Words compare as unsigned numbers.  Exactly one list holds the same
words with the same repetitions in nondecreasing order, so the specification names the result and
not a method, and stability has no effect on words.  Arrays of 0 and 1 elements are their own
result.  The specification reads "in place, using no storage beyond the array" as a call that does
not raise the heap's `top`, which `straightInsertion_bound` states, and whose call stack does not
grow, which the generated `compiled.straightInsertion.trapFree` shows by having no call-depth
premise.  That reading is weaker than the request's: a call could place its result in a free block
below `top`, and no theorem states that the result occupies the input's block.  The specification
does not distinguish Algorithm S from other sorting methods, and the program text shows the method.
The theorems concern arrays of fewer than `2^64` elements, which every array in memory is. -/

namespace Library.Sorting.StraightInsertion

def expected (xs : Array UInt64) : Array UInt64 :=
  (xs.toList.mergeSort fun a b => a ≤ b).toArray

end Library.Sorting.StraightInsertion
