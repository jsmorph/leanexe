module

public import Examples.SumCount.Program
public import TestSupport.Host

@[expose] public section

/-! The inputs of the verified compiler's cases of `sumCount`. -/

namespace Examples.SumCount

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (List UInt64) := wordArrays

end Examples.SumCount
