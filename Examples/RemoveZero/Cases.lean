import Examples.RemoveZero.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `removeZero`. -/

namespace Examples.RemoveZero

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (List UInt64) :=
  [[], [0], [0, 0], [1, 0], [7, 0, 9, 0], [1, 2, 3], [1, 2, 3, 4, 5, 6, 7, 0],
    [0, 1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 0, 0, 0, 0, 0, 0, 0, 0]]

end Examples.RemoveZero
