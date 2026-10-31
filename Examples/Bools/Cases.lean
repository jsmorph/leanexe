import Examples.Bools.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `bools`. -/

namespace Examples.Bools

open TestSupport.Host

/-- The words of the cases of `isPositive` and `mark`, and of both arguments of `same` and
`differ`. -/
def wordArgs : List UInt64 := [0, 1, 2, 3, 7, maxU - 1, maxU]

/-- The words of the cases of `flagOf` and the first word of those of `pick`. -/
def flagArgs : List UInt64 := [0, 5, maxU]

/-- The second word of the cases of `pick`. -/
def pickArgs : List UInt64 := [0, 9, maxU]

/-- The floats of the cases of `floatSame` and `inRange`. -/
def floatArgs : List Float := specialFloats ++ [1.5, -2.25, 3.0]

/-- The bounds `(lo, hi)` of the cases of `inRange`. -/
def rangeArgs : List (Float × Float) :=
  [-1.0, 0.0, nan].flatMap fun lo => [1.0, -0.0, inf].map fun hi => (lo, hi)

/-- The arguments `(n, k)` of the cases of `anyEqual`. -/
def anyEqualArgs : List (UInt64 × UInt64) :=
  [0, 1, 3, 10].flatMap fun n => [0, 2, 9, maxU].map fun k => (n, k)

end Examples.Bools
