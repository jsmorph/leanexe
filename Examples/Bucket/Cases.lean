import Examples.Bucket.Program
import Examples.Host

/-! The module cases of `bucket`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Bucket

open Examples.Host

def bucketCases : IO Unit := do
  let chosen : List (Float × Float × Float) :=
    [(5.0, 0.0, 1.0), (5.5, 0.0, 2.0), (-1.0, 0.0, 1.0), (1.0, 0.0, 0.0), (0.0, 0.0, 0.0),
     (1e300, 0.0, 1e-300), (nan, 0.0, 1.0), (1.8446744073709552e19, 0.0, 1.0), (3.0, 1.0, -1.0)]
  for (x, lo, width) in chosen ++ floatTriples do
    line "bucket" "bucket" "i64" [fl x, fl lo, fl width]
      (toString (Examples.Bucket.bucket x lo width))

def cases : IO Unit := do
  bucketCases

end Examples.Bucket
