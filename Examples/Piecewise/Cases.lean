import Examples.Piecewise.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `piecewise`. -/

namespace Examples.Piecewise

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (Float × Float × Float) :=
  [(1.0, 1.0, 2.0), (0.0, -0.0, 1.0), (0.5, 1.0, 2.0), (3.0, 1.0, 2.0), (2.0, 1.0, 2.0),
    (1.5, 1.0, 2.0), (1.5, 2.0, 1.0), (nan, 1.0, 2.0), (1.0, nan, 2.0), (1.5, 1.0, nan)] ++
    floatTriples

end Examples.Piecewise
