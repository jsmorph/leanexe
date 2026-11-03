/-! The specification of selection: the word at position `k` of the array's elements in
nondecreasing order, as Lean's `List.mergeSort` arranges them, and 0 when `k` is not a position of
the array.  Words compare as unsigned numbers.  Exactly one list holds the same words with the same
repetitions in nondecreasing order, so the word of each rank is determined, and equal words of
different positions give the same result.  The specification reads "in place" as a call that does
not raise the heap's `top`: `select_implements` bounds the rise of `top` by
`compiled.select.bound`, and `select_bound` states that the bound is 0.  It reads "a call stack
that does not grow" as the generated `compiled.select.trapFree` with no call-depth premise.  The
compiler translates recognized tail recursion into loops and gives every other recursive function
and its callers a call depth, which their theorems take as a premise, so a theorem without that
premise covers code with no recursion other than loops, whose calls nest no deeper than the
longest chain of calls in the program.  The specification does not distinguish FIND from other
selection methods, and the program text shows the method.  The theorems concern arrays of fewer
than `2^64` elements, which every array in memory is. -/

namespace Library.Sorting.Find

def expected (xs : Array UInt64) (k : UInt64) : UInt64 :=
  (xs.toList.mergeSort fun a b => a ≤ b).toArray[k.toNat]!

end Library.Sorting.Find
