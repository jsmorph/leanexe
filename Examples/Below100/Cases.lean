import Examples.Below100.Spec
import Examples.Host

/-! The module cases of `below100`, the bytes against the specification `expected`, one
line per case in the format of `tests/modules/run.sh`. -/

namespace Examples.Below100

open Examples.Host

def cases : IO Unit := do
  let max : UInt64 := 18446744073709551615
  for xs in [[], [5], [100], [99, 100, 101], [5, 100, 99, 250, 0, 7], [0, 1, 2, 3, 4, 5, 6, 7],
      [100, 200, 300, 400, 500, 600, 700, 800], [1, 2, 3, 4, 5, 6, 7, 8, 9], [max, 0, 99, 100]] do
    line "below100" "compute" "array-u64" [arrU xs]
      (words (Examples.Below100.expected xs.toArray).toList)

end Examples.Below100
