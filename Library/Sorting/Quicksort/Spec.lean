/-! The specification of sorting: the array's elements in nondecreasing order, as Lean's
`List.mergeSort` arranges them.  Words compare as unsigned numbers.  Exactly one list holds the same
words with the same repetitions in nondecreasing order, so the specification names the result and
not a method, and stability has no effect on words.  Arrays of 0 and 1 elements are their own
result.  The specification reads "in place apart from a stack of pending subfiles" as a module whose
storage beyond the array has a fixed bound: `quicksort_implements` bounds the rise of `top` by
`compiled.quicksort.bound`, and `quicksort_bound` states that the bound is the cost of one block of
128 words.  It reads "a call stack that does not grow" as the generated
`compiled.quicksort.trapFree` with no call-depth premise.  The compiler translates recognized tail
recursion into loops and gives every other recursive function and its callers a call depth, which
their theorems carry as a premise, so a theorem without that premise covers code whose calls do not
nest beyond the call graph's depth.  The specification does not distinguish Algorithm Q from other
sorting methods, and the program text shows the method.  The theorems concern arrays of fewer than
`2^64` elements, which every array in memory is. -/

namespace Library.Sorting.Quicksort

def expected (xs : Array UInt64) : Array UInt64 :=
  (xs.toList.mergeSort fun a b => a ≤ b).toArray

end Library.Sorting.Quicksort
