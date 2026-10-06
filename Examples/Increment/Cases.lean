import Examples.Increment.Spec
import Examples.Host

/-! The module cases of `increment`, the bytes against the specification `expected`, one
line per case in the format of `tests/modules/run.sh`. -/

namespace Examples.Increment

open Examples.Host

def cases : IO Unit := do
  let max : UInt64 := 18446744073709551615
  for xs in [[], [5], [0, 41, max], [1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7, 8, 9],
      [max, max, max, max, max, max, max, max]] do
    line "increment" "compute" "array-u64" [arrU xs]
      (words (Examples.Increment.expected xs.toArray).toList)

end Examples.Increment
