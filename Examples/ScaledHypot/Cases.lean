import Examples.ScaledHypot.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `scaledHypot`. -/

namespace Examples.ScaledHypot

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (Float × Float × Float) :=
  [(3.0, 4.0, 1.0), (3.0, 4.0, 0.0), (0.0, 0.0, 0.0)] ++ floatTriples

end Examples.ScaledHypot
