module

public import Examples.Axpy.Program
public import TestSupport.Host

@[expose] public section

/-! The inputs of the verified compiler's cases of `axpy`. -/

namespace Examples.Axpy

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (Float × Float × Float) := floatTriples

end Examples.Axpy
