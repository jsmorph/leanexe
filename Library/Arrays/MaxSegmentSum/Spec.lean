import Batteries.Data.List.Basic

/-! The specification of the maximum segment sum of a list of integers.  A segment of `xs` is a run
of consecutive elements of `xs`, a suffix of a prefix of `xs`.  `xs.inits` lists the prefixes of
`xs`, from `[]` to `xs`, and `List.tails` lists the suffixes of a list, from the list to `[]`, so
`(xs.inits.map List.tails).flatten` lists the segments of `xs`, the empty segment among them.
`maxSegmentSum xs` folds `max` over their sums from 0.  The empty segment has the sum 0, so the
value is at least 0, and the empty list and a list of negative integers give 0.  The definition
follows Bird's specification `maxL ∘ map sum ∘ concat ∘ map tails ∘ inits`, in which `maxL` folds
`max` from 0 (R. S. Bird, "Algebraic identities for program calculation", The Computer Journal
32(2):122–126, 1989).  Every value is an unbounded integer. -/

namespace Library.Arrays.MaxSegmentSum

def maxSegmentSum (xs : List Int) : Int :=
  ((xs.inits.map List.tails).flatten.map List.sum).foldr max 0

-- The segment `[4, -1, 2, 1]` has the greatest sum.
example : maxSegmentSum [-2, 1, -3, 4, -1, 2, 1, -5, 4] = 6 := by decide +kernel

-- Every nonempty segment has a negative sum, so the empty segment gives the maximum.
example : maxSegmentSum [-3, -1, -2] = 0 := by decide

example : maxSegmentSum [] = 0 := by decide

-- The whole list.
example : maxSegmentSum [3, -1, 4] = 6 := by decide +kernel

-- The segment `[59, 26, -53, 58, 97]`.
example : maxSegmentSum [31, -41, 59, 26, -53, 58, 97, -93, -23, 84] = 187 := by decide +kernel

end Library.Arrays.MaxSegmentSum
