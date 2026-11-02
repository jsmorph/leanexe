import Library.Sorting.Find.Spec
import TestSupport.Modules.Quicksort

/-! The inputs of the verified compiler's cases of selection. -/

namespace Library.Sorting.Find

open TestSupport.Host

/-- The pairs of an array and a rank of the verified compiler's cases, from the arrays of quicksort,
`quicksortInputs`.  Each array of at most 12 words takes every rank from 0 to its length `n`, the
first rank that is not a position.  These arrays include the empty array, `[5]`, two words in both
orders, repeated words, the words 0, `2^63 - 1`, `2^63`, and `2^64 - 1`, and arrays of 10 and 11
words in increasing and decreasing order, whose first partition puts the smallest or the largest
word at its final position.  Each longer array, up to 10,000 words, takes the ranks 0, `⌊n / 2⌋`,
`n - 1`, and `n`.  10,000 words in decreasing order, in which each partition sets aside one word,
take the rank 5,000, which needs about 10,000 partitions, so that a limit on their number below
that count changes the result.  Ten arbitrary words take the ranks `2^32 + 1`, whose low 32 bits
are 1, so that a program that reads the rank in 32 bits returns the word of rank 1 in place of 0,
and `2^64 - 1`. -/
def selectInputs : List (List UInt64 × UInt64) :=
  let all := Library.Sorting.Quicksort.quicksortInputs
  let ranks := fun (xs : List UInt64) => if xs.length ≤ 12 then List.range (xs.length + 1)
    else [0, xs.length / 2, xs.length - 1, xs.length]
  let ten := (List.range 10).map fun k => rw (k + 50000)
  let down := (List.range 10000).map fun k => UInt64.ofNat (10000 - k)
  all.flatMap (fun xs => (ranks xs).map fun k => (xs, UInt64.ofNat k)) ++
    [(down, 5000), (ten, 4294967297), (ten, maxU)]

end Library.Sorting.Find
