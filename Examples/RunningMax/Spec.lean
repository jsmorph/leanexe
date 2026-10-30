/-! The specification of the request in `Examples/RunningMax/request.txt`: entry `i` of the result
is the largest of entries `0` through `i` of the input, so the result has the input's length.

Decisions the request leaves to the specification: the numbers are unsigned 64-bit words, the
integers of the skill's types, compared as unsigned words.  The list is an array of words, the
empty input gives the empty result, and the input may have any length.  `List.foldl max 0` over a
nonempty prefix gives the prefix's largest entry, since 0 is the least word. -/

namespace Examples.RunningMax

/-- The largest of entries `0` through `i` of `input`. -/
def largestThrough (input : Array UInt64) (i : Nat) : UInt64 :=
  (input.toList.take (i + 1)).foldl max 0

def expected (input : Array UInt64) : Array UInt64 :=
  (Array.range input.size).map (largestThrough input)

end Examples.RunningMax
