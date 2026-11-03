import Library.Numerics.Arithmetic.Sieve.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of the sieve. -/

namespace Library.Numerics.Arithmetic.Sieve

/-- The bounds `N` of the cases: every `N` from 0 to 30, the squares of the primes from 7 to 37 and
of 1,009 and the numbers on either side of each, since the sieve crosses off the multiples of `p`
only when `p·p < N`, 64, 128, 1,024, 4,096, 65,536, and 65,537, the powers of 10 from 100 to
1,000,000, whose result holds 78,498 primes, 1,000,004, which follows the prime 1,000,003, and
2,000,003. -/
def sieveInputs : List UInt64 :=
  let squares := [7, 11, 13, 17, 19, 23, 29, 31, 37, 1009].flatMap fun (p : UInt64) =>
    [p * p - 1, p * p, p * p + 1]
  (List.range 31).map UInt64.ofNat ++ squares ++
    [64, 100, 128, 1000, 1024, 4096, 10000, 65536, 65537, 100000, 1000000, 1000004, 2000003]

/-- The bounds whose flags do not fit in memory, so that a call traps: `2^29 - 1`, whose flags
exceed the memory cap, and `2^29`, `2^32`, and `2^64 - 1`, which also meet the guard on the length
of an array. -/
def sieveTraps : List UInt64 := [536870911, 536870912, 4294967296, 18446744073709551615]

end Library.Numerics.Arithmetic.Sieve
