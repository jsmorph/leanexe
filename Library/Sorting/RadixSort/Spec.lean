/-! The specification of sorting: the array's elements in nondecreasing order, as Lean's
`List.mergeSort` arranges them.  Words compare as unsigned numbers.  Exactly one list holds the same
words with the same repetitions in nondecreasing order, so the specification names the result and
not a method, and stability has no effect on words.  Arrays of 0 and 1 elements are their own
result.  The specification does not distinguish radix sorting from other sorting methods, and the
program text shows the method.  The theorems of the module read the allocation requirement as a call
that raises the heap's `top` by at most a block of the array's size and a block of 256 counts, which
`radixSort_implements` and `radixSort_bound` state.  That reading is weaker than the request's:
allocations from free blocks below `top` do not raise it, and no theorem states that the call
releases the second array and the counts or that the result occupies the input's block.  They read
"a call stack that does not grow" as theorems with no call-depth premise, which rests on the
compiler's rule that the verified compiler's manual states and no theorem states: the compiler
translates recognized tail recursion and loops into loops and gives every other recursive function
and its callers a call depth, which their theorems carry as a premise.  The theorems concern arrays
of fewer than `2^64` elements, which every array in memory is. -/

namespace Library.Sorting.RadixSort

def expected (xs : Array UInt64) : Array UInt64 :=
  (xs.toList.mergeSort fun a b => a ≤ b).toArray

end Library.Sorting.RadixSort
