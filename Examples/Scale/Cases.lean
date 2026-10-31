import Examples.Scale.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `scale`. -/

namespace Examples.Scale

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (UInt64 × UInt64 × UInt64) :=
  let chosen : List (UInt64 × UInt64 × UInt64) :=
    [(6, 7, 5), (6, 7, 0), (maxU, 2, 3), (0, 0, 1), (1, 1, 1), (4294967296, 4294967296, 1),
     (9223372036854775808, 2, 1), (maxU, maxU, maxU), (5, 0, 0)]
  let random := (List.range 40).map fun i => (rw (3 * i), rw (3 * i + 1), if i % 5 = 0 then 0 else rw (3 * i + 2) % 1000)
  chosen ++ random

end Examples.Scale
