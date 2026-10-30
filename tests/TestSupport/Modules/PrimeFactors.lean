import Library.Numerics.Arithmetic.PrimeFactors.Spec
import TestSupport.Host

/-! The module cases of `primeFactors`, the bytes against the specification `expected`, one
line per case in the format of `tests/modules/run.sh`. -/

namespace Library.Numerics.Arithmetic.PrimeFactors

open TestSupport.Host

/-- The inputs of the cases, which the verified compiler's cases also use. -/
def primeFactorInputs : List UInt64 :=
  let max : UInt64 := 18446744073709551615
  [0, 1, 2, 3, 4, 60, 97, 1024, 600851475143, 1000000007, 9223372036854775808, max - 1, max]

def cases : IO Unit := do
  for n in primeFactorInputs do
    line "primeFactors" "compute" "i64" [u n] (toString (Library.Numerics.Arithmetic.PrimeFactors.expected n))

end Library.Numerics.Arithmetic.PrimeFactors
