import Examples.Bucket.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `bucket`. -/

namespace Examples.Bucket

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def samples : List (Float × Float × Float) :=
  [(5.0, 0.0, 1.0), (5.5, 0.0, 2.0), (-1.0, 0.0, 1.0), (1.0, 0.0, 0.0), (0.0, 0.0, 0.0),
    (1e300, 0.0, 1e-300), (nan, 0.0, 1.0), (1.8446744073709552e19, 0.0, 1.0), (3.0, 1.0, -1.0)] ++
    floatTriples

end Examples.Bucket
