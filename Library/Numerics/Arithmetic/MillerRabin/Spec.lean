import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! The specification of modular exponentiation and of the strong probable-prime test.
`powModSpec (x, n, m)` is `x^n mod m`, and 0 for `m = 0` as the request states, where Lean's
`x^n % 0` would be `x^n`.  Lean's power gives `0^0 = 1`, so `powModSpec (0, 0, m)` is `1 mod m`:
1 for `m ≥ 2` and 0 for `m = 1`.  For odd `n ≥ 3`, `k` is the number of factors 2 of `n - 1`, from
Mathlib's `padicValNat`, and `q = (n - 1) / 2^k` is odd.  `StrongProbablePrime n x` states that
`x^q` is 1 modulo `n` or that `x^(2^j q)` is `n - 1` modulo `n` for some `j < k`, and
`testSpec (n, x)` is 1 exactly then.  For even `n` and for `n < 3`, `testSpec` is 0.  The
definition raises the base unreduced, and `x^e mod n = (x mod n)^e mod n`, so the result depends
only on `x mod n`.  A base that `n` divides fails, since 0 is neither 1 nor `n - 1`.  The base 1
passes, since `1^q = 1`, and the base `n - 1` passes at `j = 0`, since `q` is odd. -/

namespace Library.Numerics.Arithmetic.MillerRabin

def powModSpec (x : UInt64 × UInt64 × UInt64) : UInt64 :=
  if x.2.2 = 0 then 0 else UInt64.ofNat (x.1.toNat ^ x.2.1.toNat % x.2.2.toNat)

/-- The odd number `n ≥ 3` is a strong probable prime to the base `x`. -/
def StrongProbablePrime (n x : Nat) : Prop :=
  x ^ ((n - 1) / 2 ^ padicValNat 2 (n - 1)) % n = 1 ∨
    ∃ j, j < padicValNat 2 (n - 1) ∧
      x ^ (2 ^ j * ((n - 1) / 2 ^ padicValNat 2 (n - 1))) % n = n - 1

instance (n x : Nat) : Decidable (StrongProbablePrime n x) := by
  unfold StrongProbablePrime; infer_instance

def testSpec (x : UInt64 × UInt64) : UInt64 :=
  if x.1.toNat % 2 = 1 ∧ 3 ≤ x.1.toNat ∧ StrongProbablePrime x.1.toNat x.2.toNat then 1 else 0

end Library.Numerics.Arithmetic.MillerRabin
