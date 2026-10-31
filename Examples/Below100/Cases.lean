import Examples.Below100.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `below100`. -/

namespace Examples.Below100

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (List UInt64) :=
  let max : UInt64 := 18446744073709551615
  [[], [5], [100], [99, 100, 101], [5, 100, 99, 250, 0, 7], [0, 1, 2, 3, 4, 5, 6, 7],
    [100, 200, 300, 400, 500, 600, 700, 800], [1, 2, 3, 4, 5, 6, 7, 8, 9], [max, 0, 99, 100]]

end Examples.Below100
