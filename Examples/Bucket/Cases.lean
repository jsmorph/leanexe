import Examples.Bucket.Program
import TestSupport.Host

/-! The module cases of `bucket`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Bucket

open TestSupport.Host

/-- The inputs of the cases, which the verified compiler's cases also use. -/
def samples : List (Float × Float × Float) :=
  [(5.0, 0.0, 1.0), (5.5, 0.0, 2.0), (-1.0, 0.0, 1.0), (1.0, 0.0, 0.0), (0.0, 0.0, 0.0),
    (1e300, 0.0, 1e-300), (nan, 0.0, 1.0), (1.8446744073709552e19, 0.0, 1.0), (3.0, 1.0, -1.0)] ++
    floatTriples

def bucketCases : IO Unit := do
  for (x, lo, width) in samples do
    line "bucket" "bucket" "i64" [fl x, fl lo, fl width]
      (toString (Examples.Bucket.bucket x lo width))

def cases : IO Unit := do
  bucketCases

end Examples.Bucket
