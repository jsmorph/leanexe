import Library.Sorting.StraightInsertion.Spec
import TestSupport.Modules.Heapsort

/-! The inputs of the verified compiler's cases of straight insertion. -/

namespace Library.Sorting.StraightInsertion

open TestSupport.Host

/-- The arrays of the verified compiler's cases: the inputs of heapsort, `sortInputs`, and arrays
that drive the inner loop to its ends.  `[2, 3, 4, 5, 1]` moves every earlier word for its last
insertion, and `[1, 5, 2, 3, 4]` moves one word for each of the last three.  `[3, 1, 2, 3, 3, 0]`
and `[2, 2, 1, 2, 2]` insert words equal to words already in order, and `[2^64 - 1, 0]` and
`[0, 2^64 - 1, 0]` compare the largest word with 0.  The long arrays it adds are 1,500 words in
decreasing order, which moves every earlier word at each step, 1,000 words in increasing order
except for a 0 at the end, and 1,000 words in increasing order except for the largest word at the
front. -/
def insertionInputs : List (List UInt64) :=
  let chosen : List (List UInt64) :=
    [[2, 3, 4, 5, 1], [1, 5, 2, 3, 4], [3, 1, 2, 3, 3, 0], [2, 2, 1, 2, 2], [maxU, 0], [0, maxU, 0]]
  let long : List (List UInt64) :=
    [(List.range 1500).map fun k => UInt64.ofNat (1500 - k),
      (List.range 999).map (fun k => UInt64.ofNat (k + 1)) ++ [0],
      maxU :: (List.range 999).map fun k => UInt64.ofNat k]
  Library.Sorting.Heapsort.sortInputs ++ chosen ++ long

end Library.Sorting.StraightInsertion
