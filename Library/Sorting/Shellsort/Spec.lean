/-! The specification of sorting: the array's elements in nondecreasing order, as Lean's
`List.mergeSort` arranges them.  Words compare as unsigned numbers.  Exactly one list holds the same
words with the same repetitions in nondecreasing order, so the specification names the result and
not a method, and stability has no effect on words.  Arrays of 0 and 1 elements are their own
result.  The specification reads "in place" as a call that does not raise the heap's `top`:
`shellsort_implements` bounds the rise of `top` by `compiled.shellsort.bound`, and `shellsort_bound`
states that the bound is 0.  That reading is weaker than the request's: a call could place its
result in a free block below `top`, and no theorem states that the result occupies the input's
block.  The specification reads "a call stack that does not grow" as theorems with no call-depth
premise, which depends on the compiler's rule that the verified compiler's manual states and no
theorem states: the compiler translates recognized tail recursion into loops and gives every other
recursive function and its callers a call depth, which their theorems take as a premise.  The
specification does not distinguish Algorithm D or its increments from other sorting methods, and the
program text shows the method.  The theorems concern arrays of fewer than `2^64` elements, which
every array in memory is. -/

namespace Library.Sorting.Shellsort

def expected (xs : Array UInt64) : Array UInt64 :=
  (xs.toList.mergeSort fun a b => a ≤ b).toArray

end Library.Sorting.Shellsort
