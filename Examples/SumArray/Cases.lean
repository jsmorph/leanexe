import Examples.SumArray.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `sumArray`. -/

namespace Examples.SumArray

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (List UInt64) := wordArrays

end Examples.SumArray
