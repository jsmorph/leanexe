import Examples.PairSum.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `pairSum`. -/

namespace Examples.PairSum

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (UInt64 × UInt64) :=
  let chosen : List (UInt64 × UInt64) := [(3, 4), (maxU, 2), (0, 0), (maxU, maxU)]
  let random := (List.range 30).map fun i => (rw (2 * i + 300), rw (2 * i + 301))
  chosen ++ random

end Examples.PairSum
