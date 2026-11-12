import Library.Numerics.Interval.Enclose

/-!
TRIAD's formulas over the real numbers, each with its interval program.  Each `enclosure_def`
declares a real function, the interval function `fI`, and the theorem `f.encloses`.  `frameOf`
gives the lengths of `a` and of `a × b` and the nine components of TRIAD's frame of `a` and `b`,
`matrixOf` the entries of the map between two frames, row by row, and `boundOf` the quantities
`x = sin (ε1 + ε2) / sin θ` and `h` of the error bound.  `Model.lean` states the same quantities
with vectors, and `Soundness.lean` relates the two.
-/

open Real

namespace Demos.Attitude.Spec

/-- The lengths of `a` and of `a × b`, `ā`, the unit normal `n` of `a` and `b`, and `ā × n`. -/
enclosure_def frameOf (a1 a2 a3 c1 c2 c3) :=
  let na := √(a1 * a1 + a2 * a2 + a3 * a3)
  let t1 := a1 / na
  let t2 := a2 / na
  let t3 := a3 / na
  let x1 := a2 * c3 - a3 * c2
  let x2 := a3 * c1 - a1 * c3
  let x3 := a1 * c2 - a2 * c1
  let nx := √(x1 * x1 + x2 * x2 + x3 * x3)
  let n1 := x1 / nx
  let n2 := x2 / nx
  let n3 := x3 / nx
  (na, nx, t1, t2, t3, n1, n2, n3, t2 * n3 - t3 * n2, t3 * n1 - t1 * n3, t1 * n2 - t2 * n1)

/-- The entries, row by row, of the map that sends the frame `t` to the frame `s`: entry `jk` is
`Σ_i s_ij t_ik`. -/
enclosure_def matrixOf (t11 t12 t13 t21 t22 t23 t31 t32 t33 s11 s12 s13 s21 s22 s23 s31 s32 s33) :=
  (s11 * t11 + s21 * t21 + s31 * t31, s11 * t12 + s21 * t22 + s31 * t32,
    s11 * t13 + s21 * t23 + s31 * t33, s12 * t11 + s22 * t21 + s32 * t31,
    s12 * t12 + s22 * t22 + s32 * t32, s12 * t13 + s22 * t23 + s32 * t33,
    s13 * t11 + s23 * t21 + s33 * t31, s13 * t12 + s23 * t22 + s33 * t32,
    s13 * t13 + s23 * t23 + s33 * t33)

/-- `x = sin (ε1 + ε2) / sin θ` for the references `p` and `q`, and
`h = sin²(ε1/2) + cos²(ε1/2) x² / (2 (1 + √(1 - x²)))`. -/
enclosure_def boundOf (e1 e2 p1 p2 p3 q1 q2 q3) :=
  let np := √(p1 * p1 + p2 * p2 + p3 * p3)
  let nq := √(q1 * q1 + q2 * q2 + q3 * q3)
  let x1 := p2 * q3 - p3 * q2
  let x2 := p3 * q1 - p1 * q3
  let x3 := p1 * q2 - p2 * q1
  let st := √(x1 * x1 + x2 * x2 + x3 * x3) / (np * nq)
  let x := sin (e1 + e2) / st
  let s := sin (e1 / 2)
  let c := cos (e1 / 2)
  (x, s * s + c * c * (x * x / (2 * (1 + √(1 - x * x)))))

/-- The lengths of `b1`, `b1 × b2`, `r1`, and `r1 × r2`, and TRIAD's matrix row by row. -/
enclosure_def triadOf (b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z) :=
  let (nb, nbx, t11, t12, t13, t21, t22, t23, t31, t32, t33) := frameOf b1x b1y b1z b2x b2y b2z
  let (nr, nrx, s11, s12, s13, s21, s22, s23, s31, s32, s33) := frameOf r1x r1y r1z r2x r2y r2z
  let (m11, m12, m13, m21, m22, m23, m31, m32, m33) :=
    matrixOf t11 t12 t13 t21 t22 t23 t31 t32 t33 s11 s12 s13 s21 s22 s23 s31 s32 s33
  (nb, nbx, nr, nrx, m11, m12, m13, m21, m22, m23, m31, m32, m33)

end Demos.Attitude.Spec
