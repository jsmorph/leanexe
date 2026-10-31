import Library.Numerics.Arithmetic.PrimeFactors.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `primeFactors`. -/

namespace Library.Numerics.Arithmetic.PrimeFactors

open TestSupport.Host

/-- The inputs of the verified compiler's cases. -/
def primeFactorInputs : List UInt64 :=
  let max : UInt64 := 18446744073709551615
  [0, 1, 2, 3, 4, 60, 97, 1024, 600851475143, 1000000007, 9223372036854775808, max - 1, max]

end Library.Numerics.Arithmetic.PrimeFactors
