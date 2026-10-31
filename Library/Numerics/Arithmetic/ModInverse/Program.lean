/-! The modular inverse by the extended Euclidean algorithm, Algorithm X of TAOCP §4.5.2, keeping
only the coefficient of `a`.  The remainders `r0 > r1` start at `m` and `a mod m`.  Their
coefficients alternate in sign, so the program keeps their magnitudes `t0` and `t1` and a parity
word `p`: when `p = 1`, `a * t1 ≡ r1` and `a * t0 ≡ -r0` modulo `m`, and when `p = 0` the signs are
reversed.  The magnitudes satisfy `t1 * r0 + t0 * r1 = m`, so none exceeds `m` and no word wraps.
When `r1` reaches 0, `r0` is the greatest common divisor of `a` and `m`, and when it is 1 the
inverse is `t0` or `m - t0`, by the sign. -/

namespace Library.Numerics.Arithmetic.ModInverse

/-- The loop of Algorithm X on the remainders `r0`, `r1`, their coefficients' magnitudes `t0`,
`t1`, and the parity `p`, for the modulus `m`. -/
def euclid (m r0 r1 t0 t1 p : UInt64) : UInt64 :=
  if r1 = 0 then
    if r0 = 1 then (if p = 1 then (m - t0) % m else t0 % m) else 0
  else euclid m r1 (r0 % r1) t1 (t0 + r0 / r1 * t1) (1 - p)
termination_by r1.toNat
decreasing_by
  have h : ¬ r1 = 0 := by assumption
  have h0 : r1.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
  rw [UInt64.toNat_mod]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero h0)

/-- The inverse of `a` modulo `m`, or 0 when it does not exist. -/
def modInverse (a m : UInt64) : UInt64 :=
  if m ≤ 1 then 0 else euclid m m (a % m) 0 1 1

end Library.Numerics.Arithmetic.ModInverse
