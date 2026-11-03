/-! The specification of sorting: the array's elements in nondecreasing order, as Lean's
`List.mergeSort` arranges them.  Words compare as unsigned numbers.  Exactly one list holds the same
words with the same repetitions in nondecreasing order, so the specification names the result and
not a method, and stability has no effect on words.  Arrays of 0 and 1 elements are their own
result.  The specification reads "no storage beyond the array" as a call that does not raise the
heap's `top`, which a separate theorem states, and that uses a fixed number of locals.  That reading
is weaker than the request's: a call could place its result in a free block below `top`, and no
theorem states that the result occupies the input's block.  The compiler translates the sift into a
loop, so the call stack does not grow.  The specification cannot state that the program follows
Algorithm H, which the program text shows. -/

namespace Library.Sorting.Heapsort

def expected (xs : Array UInt64) : Array UInt64 :=
  (xs.toList.mergeSort fun a b => a ≤ b).toArray

end Library.Sorting.Heapsort
