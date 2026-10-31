import Examples.Increment.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `increment`. -/

namespace Examples.Increment

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (List UInt64) :=
  let max : UInt64 := 18446744073709551615
  [[], [5], [0, 41, max], [1, 2, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7, 8, 9],
    [max, max, max, max, max, max, max, max]]

end Examples.Increment
