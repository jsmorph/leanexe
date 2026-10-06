import Examples.Lookup.Spec
import Examples.Host

/-! The module cases of `lookup`, the bytes against the specification `expected`, one
line per case in the format of `tests/modules/run.sh`. -/

namespace Examples.Lookup

open Examples.Host

def cases : IO Unit := do
  let max : UInt64 := 18446744073709551615
  let pairs : List UInt64 := [1, 10, 42, 20, 42, 30, 4, 40, 5, 50, 6, 60, 7, 70, 8, 80, 9, 90, 10, 100]
  for xs in [42 :: pairs, 99 :: pairs, 10 :: pairs, 1 :: pairs, List.replicate 21 0, pairs,
      42 :: pairs ++ [0], [], [max, 3, 4, max, max, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] do
    line "lookup" "compute" "array-u64" [arrU xs] (words (Examples.Lookup.expected xs.toArray).toList)

end Examples.Lookup
