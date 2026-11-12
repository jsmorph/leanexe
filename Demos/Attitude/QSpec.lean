import Library.Numerics.Interval.Enclose

/-!
The q-method's formulas over the real numbers, each with its interval program.  Each
`enclosure_def` declares a real function, the interval function `fI`, and the theorem
`f.encloses`.  `obsScale`, `obsFirst`, `obsRest`, and `obsTrue` give one observation's terms:
the lengths of `b` and `r`, the entries of `k K(b, r)` with `k = a / (|b| |r|)`, which equal those
of `a K(b̄, r̄)`, and `a sin ε` and `a cos ε`.  `schur4`, `schur3`, and `schur2` eliminate the first
index of a symmetric matrix, `applyK` multiplies a symmetric 4×4 matrix by a quaternion,
`residOf` gives the squared length, the Rayleigh quotient, and the squared relative residual of
the quaternion, and `boundsOf` the gaps to the cut and the sines of the two bounds.
`Davenport.lean` and `Inertia.lean` state the same quantities with matrices, and
`QSoundness.lean` relates the two.
-/

open Real

namespace Demos.Attitude.QMethod.Spec

/-- The lengths of `b` and `r`, and `k = a / (|b| |r|)`. -/
enclosure_def obsScale (b1 b2 b3 r1 r2 r3 a) :=
  let nb := √(b1 * b1 + b2 * b2 + b3 * b3)
  let nr := √(r1 * r1 + r2 * r2 + r3 * r3)
  (nb, nr, a / (nb * nr))

/-- The first row of `k K(b, r)`: `k (r · b)` and `k (b × r)`. -/
enclosure_def obsFirst (b1 b2 b3 r1 r2 r3 k) :=
  (k * (r1 * b1 + r2 * b2 + r3 * b3), k * (b2 * r3 - b3 * r2), k * (b3 * r1 - b1 * r3),
    k * (b1 * r2 - b2 * r1))

/-- The lower right block of `k K(b, r)`, row by row, for `s = k (r · b)`. -/
enclosure_def obsRest (b1 b2 b3 r1 r2 r3 k s) :=
  (k * (2 * (r1 * b1)) - s, k * (r1 * b2 + r2 * b1), k * (r1 * b3 + r3 * b1),
    k * (2 * (r2 * b2)) - s, k * (r2 * b3 + r3 * b2), k * (2 * (r3 * b3)) - s)

/-- `a sin ε` and `a cos ε`. -/
enclosure_def obsTrue (a e) := (a * sin e, a * cos e)

/-- The Schur complement of the entry `a00` of a symmetric 4×4 matrix. -/
enclosure_def schur4 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33) :=
  let l1 := a01 / a00
  let l2 := a02 / a00
  let l3 := a03 / a00
  (a11 - l1 * a01, a12 - l1 * a02, a13 - l1 * a03, a22 - l2 * a02, a23 - l2 * a03,
    a33 - l3 * a03)

/-- The Schur complement of the entry `c00` of a symmetric 3×3 matrix. -/
enclosure_def schur3 (c00 c01 c02 c11 c12 c22) :=
  let l1 := c01 / c00
  let l2 := c02 / c00
  (c11 - l1 * c01, c12 - l1 * c02, c22 - l2 * c02)

/-- The last pivot of a symmetric 2×2 matrix. -/
enclosure_def schur2 (d00 d01 d11) := d11 - d01 / d00 * d01

/-- `K p` for the symmetric `K` and the quaternion `p = (w, x, y, z)`. -/
enclosure_def applyK (k00 k01 k02 k03 k11 k12 k13 k22 k23 k33 w x y z) :=
  (k00 * w + k01 * x + k02 * y + k03 * z, k01 * w + k11 * x + k12 * y + k13 * z,
    k02 * w + k12 * x + k22 * y + k23 * z, k03 * w + k13 * x + k23 * y + k33 * z)

/-- For `u = K p`: `|p|²`, the Rayleigh quotient `μ = pᵀ u / |p|²`, and the squared relative
residual `|u - μ p|² / |p|²`. -/
enclosure_def residOf (u0 u1 u2 u3 w x y z) :=
  let n2 := w * w + x * x + y * y + z * z
  let mu := (w * u0 + x * u1 + y * u2 + z * u3) / n2
  let r0 := u0 - mu * w
  let r1 := u1 - mu * x
  let r2 := u2 - mu * y
  let r3 := u3 - mu * z
  (n2, mu, (r0 * r0 + r1 * r1 + r2 * r2 + r3 * r3) / n2)

/-- The gaps `μ - c` and `μt - c` to the cut `c`, and the sines `ρ / (μ - c)` and
`ρt / (μt - c)` of the two bounds. -/
enclosure_def boundsOf (mu rho rt mt c) :=
  let g := mu - c
  let gt := mt - c
  (g, gt, rho / g, rt / gt)

end Demos.Attitude.QMethod.Spec
