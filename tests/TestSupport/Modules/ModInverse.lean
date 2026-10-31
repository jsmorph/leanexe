import Library.Numerics.Arithmetic.ModInverse.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of the modular inverse. -/

namespace Library.Numerics.Arithmetic.ModInverse

open TestSupport.Host

/-- The arguments `(a, m)` of the verified compiler's cases.  The modulus 0 is paired with 0, 1, 5,
and `2^64 - 1`, and the modulus 1 with 0, 1, and `2^64 - 1`.  Each small modulus, 2, 3, 4, 6, 7,
10, 12, and 97, is paired with every `a` from 0 to `m + 2` and with `2^64 - 1`.  The other moduli are the primes `2^61 - 1`,
`2^64 - 59`, and `10^9 + 7`, the odd composite `2^64 - 1`, the even modulus `2^63`, the composite
600851475143, and two arbitrary words, one forced odd.  Each is paired with 0, 1, 2, `m - 1`, `m`,
`m + 1`, `2^64 - 1`, and twelve arbitrary words; for `m = 2^64 - 1`, `m + 1` wraps to 0 and
`2^64 - 1` is `m`, so two pairs repeat.  The consecutive Fibonacci numbers `F₉₂` and `F₉₃`, on which
the algorithm reaches the largest number of steps of any pair of words, are paired in both
orders. -/
def inverseInputs : List (UInt64 × UInt64) :=
  let small : List UInt64 := [2, 3, 4, 6, 7, 10, 12, 97]
  let large : List UInt64 :=
    [2305843009213693951, 18446744073709551557, maxU, 9223372036854775808, 1000000007,
      600851475143, rw 900, rw 901 ||| 1]
  let edge : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (5, 0), (maxU, 0), (0, 1), (1, 1), (maxU, 1),
      (7540113804746346429, 12200160415121876738), (12200160415121876738, 7540113804746346429)]
  let smallPairs := small.flatMap fun m =>
    ((List.range (m.toNat + 3)).map fun a => (UInt64.ofNat a, m)) ++ [(maxU, m)]
  let largePairs := large.flatMap fun m =>
    ([0, 1, 2, m - 1, m, m + 1, maxU] ++ (List.range 12).map fun i => rw (17 * i + m.toNat % 1000))
      |>.map fun a => (a, m)
  edge ++ smallPairs ++ largePairs

end Library.Numerics.Arithmetic.ModInverse
