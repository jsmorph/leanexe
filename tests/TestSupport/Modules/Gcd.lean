import Library.Numerics.Arithmetic.Gcd.Program
import Library.Numerics.Arithmetic.Gcd.Spec
import TestSupport.Host

/-! The module cases of `gcd`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Library.Numerics.Arithmetic.Gcd

open TestSupport.Host

/-- The arguments of the cases, which the verified compiler's cases also use. -/
def gcdPairs : List (UInt64 × UInt64) :=
  let chosen : List (UInt64 × UInt64) :=
    [(48, 18), (0, 0), (0, 5), (5, 0), (1, maxU), (maxU, maxU - 1), (9223372036854775808, 3),
     (12157665459056928801, 7540113804746346429), (1071, 462)]
  let random := (List.range 40).map fun i => (rw (2 * i + 100), if i % 7 = 0 then 0 else rw (2 * i + 101) % 100000)
  chosen ++ random

def gcdCases : IO Unit := do
  for (a, b) in gcdPairs do
    line "gcd" "gcd" "i64" [u a, u b] (toString (Library.Numerics.Arithmetic.Gcd.expected (a, b)))

def cases : IO Unit := do
  gcdCases

end Library.Numerics.Arithmetic.Gcd
