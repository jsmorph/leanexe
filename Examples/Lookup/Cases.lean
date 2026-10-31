import Examples.Lookup.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `lookup`. -/

namespace Examples.Lookup

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (List UInt64) :=
  let max : UInt64 := 18446744073709551615
  let pairs : List UInt64 := [1, 10, 42, 20, 42, 30, 4, 40, 5, 50, 6, 60, 7, 70, 8, 80, 9, 90, 10, 100]
  [42 :: pairs, 99 :: pairs, 10 :: pairs, 1 :: pairs, List.replicate 21 0, pairs,
    42 :: pairs ++ [0], [], [max, 3, 4, max, max, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

end Examples.Lookup
