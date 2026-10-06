import Examples.RemoveZero.Spec
import Examples.Host

/-! The module cases of `removeZero`, the bytes against the specification `expected`, one
line per case in the format of `tests/modules/run.sh`. -/

namespace Examples.RemoveZero

open Examples.Host

def cases : IO Unit := do
  for xs in [[], [0], [0, 0], [1, 0], [7, 0, 9, 0], [1, 2, 3], [1, 2, 3, 4, 5, 6, 7, 0],
      [0, 1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0]] do
    line "removeZero" "compute" "array-u64" [arrU xs]
      (words (Examples.RemoveZero.expected xs.toArray).toList)

end Examples.RemoveZero
