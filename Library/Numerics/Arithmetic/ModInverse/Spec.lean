import Mathlib.Data.ZMod.Basic

/-! The specification of the modular inverse.  For `m ≥ 2` and `a` coprime to `m`, the inverse of
`a` modulo `m` is the value in `[0, m)` of the inverse of `a` in `ZMod m`, the integers modulo `m`.
Every other pair has no inverse in `[0, m)` except when `m = 1`, where 0 is the inverse of every
`a`, and `expected` returns 0 in each of these cases.  For `m = 0` no value lies in `[0, m)`.  For
`m ≥ 2` and `a` not coprime to `m`, no `x` has `a * x` congruent to 1.  For `m ≥ 2`, 0 is never an
inverse, so the result 0 signals that no inverse exists, while for `m = 1` the result 0 is the
inverse.  The congruence is one of integers: `a` may exceed
`m`, and the product `a * x` does not wrap.  The specification fixes the result and not the method,
so the program text alone shows that the module uses the extended Euclidean algorithm. -/

namespace Library.Numerics.Arithmetic.ModInverse

def expected (x : UInt64 × UInt64) : UInt64 :=
  if 2 ≤ x.2.toNat ∧ Nat.Coprime x.1.toNat x.2.toNat then
    UInt64.ofNat ((x.1.toNat : ZMod x.2.toNat)⁻¹).val
  else 0

end Library.Numerics.Arithmetic.ModInverse
