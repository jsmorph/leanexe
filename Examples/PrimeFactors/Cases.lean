import Examples.PrimeFactors.Spec
import Examples.Host

/-! The module cases of `primeFactors`, the bytes against the specification `expected`, one
line per case in the format of `tests/modules/run.sh`. -/

namespace Examples.PrimeFactors

open Examples.Host

def cases : IO Unit := do
  let max : UInt64 := 18446744073709551615
  for n in [0, 1, 2, 3, 4, 60, 97, 1024, 600851475143, 1000000007, 9223372036854775808, max - 1,
      max] do
    line "primeFactors" "compute" "i64" [u n] (toString (Examples.PrimeFactors.expected n))

end Examples.PrimeFactors
