import Mathlib.Data.List.Sort

/-! The specification of the next arrangement.  Arrangements are compared in the lexicographic order
of Lean's lists, `<` on `List UInt64`, with words compared as unsigned numbers.  An arrangement of
`xs` is a list with the same words and the same repetitions, `List.Perm`.  `IsNext xs r` states that
the pair `r` of a flag and an array is the result that the request asks for: when some arrangement
of `xs` is greater than `xs`, the flag is 1 and the array is the least such arrangement, and
otherwise the flag is 0 and the array is the least arrangement, the words in nondecreasing order as
`List.mergeSort` arranges them.  The lexicographic order is total on lists of words, so
`IsNext xs r` determines `r`, which `isNext_unique` states.  An array of 0 or 1 words has no greater
arrangement, and its result is itself with the flag 0.  The theorems of the module read "in place"
as a call that does not raise the heap's `top`: `nextPerm_implements` bounds the rise of `top` by
`compiled.nextPerm.bound`, and `nextPerm_bound` states that the bound is 0.  That reading is weaker
than the request's: a call could place its result in a free block below `top`, and no theorem states
that the result occupies the input's block.  They read "a call stack that does not grow" as the
absence of a call-depth premise from `nextPerm_implements`, which depends on the compiler's rule
that the verified compiler's manual states and no theorem states: the compiler translates recognized
tail recursion into loops and gives every other recursive function and its callers a call depth,
which their theorems take as a premise.  The specification does not distinguish Algorithm L from
other ways to find the next arrangement, and the program text shows the method. -/

namespace Library.Combinatorics.NextPermutation

/-- `ys` is an arrangement of `xs` greater than `xs`. -/
def Greater (xs ys : List UInt64) : Prop := ys.Perm xs ∧ xs < ys

/-- The flag and the array of the next arrangement of `xs`. -/
def IsNext (xs : Array UInt64) (r : UInt64 × Array UInt64) : Prop :=
  ((∃ zs, Greater xs.toList zs) →
    r.1 = 1 ∧ Greater xs.toList r.2.toList ∧ ∀ zs, Greater xs.toList zs → ¬zs < r.2.toList) ∧
  ((¬∃ zs, Greater xs.toList zs) →
    r.1 = 0 ∧ r.2.toList = xs.toList.mergeSort fun a b => a ≤ b)

end Library.Combinatorics.NextPermutation
