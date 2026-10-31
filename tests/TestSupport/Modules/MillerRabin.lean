import Library.Numerics.Arithmetic.MillerRabin.Spec
import TestSupport.Host
import Mathlib.Tactic

/-! The inputs of the verified compiler's cases of modular exponentiation and the strong
probable-prime test. -/

namespace Library.Numerics.Arithmetic.MillerRabin

open TestSupport.Host

/-- The triples `(x, n, m)` of `powMod`.  The modulus 0, the modulus 1, small moduli with bases
above and below them, the exponents 0, 1, and `2^64 - 1`, the exponent 0 with the moduli 0, 1, 7,
and 13, the base 0, the moduli `2^63`, `2^64 - 2`, `2^64 - 1`, and the primes `2^61 - 1` and
`2^64 - 59`, Fermat's little theorem for a prime modulus, and arbitrary words as base, exponent, and
modulus, the first of which is 12345. -/
def powInputs : List (UInt64 × UInt64 × UInt64) :=
  let half : UInt64 := 9223372036854775808
  let p61 : UInt64 := 2305843009213693951
  let p64 : UInt64 := 18446744073709551557
  [(5, 3, 0), (5, 3, 1), (2, 10, 1000), (7, 0, 13), (7, 1, 13), (20, 3, 13), (0, 5, 7), (0, 0, 7),
    (7, 0, 1), (7, 0, 0), (0, 0, 1), (0, 0, 0), (3, maxU, 7), (maxU, maxU, maxU), (maxU, 2, half),
    (3, 200, half), (2, p61 - 1, p61), (12345, p64 - 1, p64), (maxU, maxU, p64), (p64 - 1, 2, p64),
    (half + 1, half, maxU - 1)] ++
    (List.range 30).map fun i => (rw (3 * i), rw (3 * i + 1), rw (3 * i + 2))

/-- The pairs `(n, x)` of the test.  Even numbers, among them `2^63` and `2^64 - 2`, with bases such
as 1 and 5 for which `x^(n - 1)` is 1 modulo `n`, and with 3 for `n = 4`, for which `x^(n - 1)` is
`n - 1`; the numbers 0, 1, and 2; small primes and composites; the Carmichael number 561, which
fails to base 2; the strong pseudoprime 2047 to base 2, which fails to base 3, and 3215031751 to the
bases 2, 3, 5, and 7, which fails to base 11; the strong pseudoprimes 3277, 4033, and 8321 to base
2, which pass at `j = 1`, and 65281, which passes at `j = 3`; the primes 17, 97, and 65537 with
bases that pass at `j = 2`, 3, 4, and 15, and the prime `15564440312192434177 = 27 * 2^59 + 1`
with the base 2, which passes at `j = 57`, and the base 5, which passes at `j = 58`; the bases 0,
1, `n - 1`, `n`, and words above `n`, for `n = 13` and `n = 2^64 - 59`; `2^63 + 1`, whose `n - 1`
has 63 factors 2, with the bases 2 and 3 and with 8881765665119413741, a square root of 1 other
than 1 and `n - 1` modulo `n`; `2^32 + 1`, whose `n - 1` has 32 factors 2; the primes `2^61 - 1`
and `2^64 - 59`; the composite `2^64 - 1`; and arbitrary odd words with arbitrary bases, the first
of which is 12345. -/
def testInputs : List (UInt64 × UInt64) :=
  let p61 : UInt64 := 2305843009213693951
  let p64 : UInt64 := 18446744073709551557
  let big : UInt64 := 15564440312192434177
  let half1 : UInt64 := 9223372036854775809
  [(0, 2), (1, 2), (2, 3), (4, 3), (4, 1), (4, 5), (100, 7), (100, 1), (half1 - 1, 3),
    (maxU - 1, 3), (maxU - 1, 1), (3, 2), (5, 2), (7, 3), (9, 2), (15, 2), (561, 2), (2047, 2),
    (2047, 3), (3215031751, 2), (3215031751, 3), (3215031751, 5), (3215031751, 7),
    (3215031751, 11), (3277, 2), (4033, 2), (8321, 2), (65281, 2), (17, 2), (17, 3), (97, 5),
    (65537, 3), (big, 2), (big, 5), (13, 0), (13, 1), (13, 12), (13, 13), (13, 100), (p64, 0),
    (p64, 1), (p64, p64 - 1), (p64, p64), (half1, 2), (half1, 3), (half1, 8881765665119413741),
    (4294967297, 3), (p61, 2), (p61, 37), (p64, 2), (p64, maxU), (maxU, 2), (maxU, 3)] ++
    (List.range 30).map fun i => (rw (2 * i) ||| 1, rw (2 * i + 1))

/-- `x^n % m` by repeated squaring, for the expected values of the cases: the specification states
`x^n % m` directly, which no machine can evaluate for exponents near `2^64`. -/
def refPow (x n m : Nat) : Nat :=
  if n = 0 then 1 % m
  else if n % 2 = 0 then refPow x (n / 2) m * refPow x (n / 2) m % m
  else refPow x (n / 2) m * refPow x (n / 2) m % m * (x % m) % m
termination_by n
decreasing_by all_goals omega

theorem refPow_eq (x n m : Nat) : refPow x n m = x ^ n % m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [refPow]
    split
    · rename_i h; rw [h]; simp
    · have hih := ih (n / 2) (by omega)
      have hn : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
      split
      · rename_i h2
        have e : x ^ n = x ^ (n / 2) * x ^ (n / 2) := by
          conv_lhs => rw [hn, h2, Nat.add_zero]
          ring
        rw [hih, e, Nat.mul_mod (x ^ (n / 2)) (x ^ (n / 2)) m]
      · rename_i h2
        have e : x ^ n = x ^ (n / 2) * x ^ (n / 2) * x := by
          conv_lhs => rw [hn, show n % 2 = 1 by omega]
          ring
        rw [hih, e, Nat.mul_mod (x ^ (n / 2) * x ^ (n / 2)) x m,
          Nat.mul_mod (x ^ (n / 2)) (x ^ (n / 2)) m]

/-- `powModSpec` with `refPow` in place of the power. -/
def powModRef (x : UInt64 × UInt64 × UInt64) : UInt64 :=
  if x.2.2 = 0 then 0 else UInt64.ofNat (refPow x.1.toNat x.2.1.toNat x.2.2.toNat)

theorem powModRef_eq (x : UInt64 × UInt64 × UInt64) : powModRef x = powModSpec x := by
  unfold powModRef powModSpec; rw [refPow_eq]

/-- `testSpec` with `refPow` in place of the powers. -/
def testRef (x : UInt64 × UInt64) : UInt64 :=
  if x.1.toNat % 2 = 1 ∧ 3 ≤ x.1.toNat ∧
      (refPow x.2.toNat ((x.1.toNat - 1) / 2 ^ padicValNat 2 (x.1.toNat - 1)) x.1.toNat = 1 ∨
        ∃ j, j < padicValNat 2 (x.1.toNat - 1) ∧
          refPow x.2.toNat (2 ^ j * ((x.1.toNat - 1) / 2 ^ padicValNat 2 (x.1.toNat - 1)))
            x.1.toNat = x.1.toNat - 1) then 1 else 0

theorem testRef_eq (x : UInt64 × UInt64) : testRef x = testSpec x := by
  unfold testRef testSpec StrongProbablePrime
  simp only [refPow_eq]

end Library.Numerics.Arithmetic.MillerRabin
