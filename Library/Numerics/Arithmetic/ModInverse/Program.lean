/-! The modular inverse by the extended Euclidean algorithm, Algorithm X of TAOCP §4.5.2, with
Knuth's `u = m` and `v = a`, keeping only the coefficient of `a`.  The remainders `r0 > r1`,
Knuth's `u3` and `v3`, start at `m` and `a mod m`, where Knuth's step X1 starts `v3` at `v`:
reducing `a` first makes `r0 > r1` hold from the first step and changes no congruence modulo `m`.
Knuth's coefficients `u2` and `v2` alternate in sign, so the program keeps their magnitudes `t0`
and `t1` and a parity word `p`: when `p = 1`, `a * t1 ≡ r1` and `a * t0 ≡ -r0` modulo `m`, and
when `p = 0` the signs are reversed.  The magnitudes satisfy `t1 * r0 + t0 * r1 = m`, so none
exceeds `m` and no word wraps.  When `r1` reaches 0, `r0` is the greatest common divisor of `a` and
`m`, and when it is 1 the inverse is `t0` or `m - t0`, by the sign. -/

namespace Library.Numerics.Arithmetic.ModInverse

/-- Steps X2 and X3 for the modulus `m`, on the remainders `r0` and `r1`, the magnitudes `t0` and
`t1` of their coefficients of `a`, and the parity `p` of the sign.  Step X2 stops when `r1` is 0,
and the result is then the inverse of `a` modulo `m` when `r0` is 1, `m - t0` or `t0` by the
parity, and 0 otherwise.  For `m > 0`, the reduction modulo `m` puts the result in `[0, m)` for all
values of the other arguments.  Step X3 replaces `(r0, r1)` by `(r1, r0 mod r1)` and `(t0, t1)` by
`(t1, t0 + q * t1)` with `q = r0 / r1`, and flips `p`. -/
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

/-- Step X1 and the loop: the inverse of `a` modulo `m` in `[0, m)`, or 0 when none exists.  For
`m ≤ 1` the result is 0, which for `m = 1` is the inverse.  Otherwise `euclid` starts with
`r0 = m`, `r1 = a mod m`, `t0 = 0`, `t1 = 1`, and `p = 1`. -/
def modInverse (a m : UInt64) : UInt64 :=
  if m ≤ 1 then 0 else euclid m m (a % m) 0 1 1

end Library.Numerics.Arithmetic.ModInverse
