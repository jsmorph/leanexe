import Examples.Axpy.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `axpy`. -/

namespace Examples.Axpy

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (Float × Float × Float) := floatTriples

end Examples.Axpy
