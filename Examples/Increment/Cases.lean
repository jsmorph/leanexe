import Examples.Increment.Spec
import TestSupport.Host

/-! The module cases of `increment`, the bytes against the specification `expected`, one
line per case in the format of `tests/modules/run.sh`. -/

namespace Examples.Increment

open TestSupport.Host

/-- The inputs of the cases, which the verified compiler's cases also use. -/
def samples : List (List UInt64) :=
  let max : UInt64 := 18446744073709551615
  [[], [5], [0, 41, max], [1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7, 8, 9],
    [max, max, max, max, max, max, max, max]]

def cases : IO Unit := do
  for xs in samples do
    line "increment" "compute" "array-u64" [arrU xs]
      (words (Examples.Increment.expected xs.toArray).toList)

end Examples.Increment
