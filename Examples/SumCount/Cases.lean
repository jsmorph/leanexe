import Examples.SumCount.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `sumCount`. -/

namespace Examples.SumCount

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (List UInt64) := wordArrays

end Examples.SumCount
