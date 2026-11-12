import Demos.Attitude.Spec
import Library.Numerics.Float64.Asin.Program

/-!
TRIAD with an error bound.  `triadWith` evaluates TRIAD's frames and matrix on the point intervals
of the inputs, checks that the lengths of the vectors and of their cross products are positive,
and then computes the bound: the interval of `2 arcsin √h`, with `h` from `Spec.boundOf`, plus the
interval of `arcsin (η / (1 - η))`, where `η` is the root of the sum of the squared widths of the
nine intervals of the matrix.  `triad` passes the tables of the library's `sin` and `cos`, and
`Soundness.lean` states what each status implies.

| Status | Meaning |
|---|---|
| 0 | The intervals contain TRIAD's matrix, and `err` bounds the error of every matrix in them. |
| 1 | No result: a non-finite vector component, a vector or cross product too short, or an overflow. |
| 2 | The intervals contain TRIAD's matrix, and the error bounds or the geometry admit no bound. |
-/

namespace Demos.Attitude

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-- The arcsines of the points of an interval that lies in `[-1, 1]`, and a rejection otherwise. -/
def asinI (a : Interval) : Interval :=
  if a.status == 0 && -1.0 ≤ a.lo && a.hi ≤ 1.0 then
    increasing a (Asin.asin a.lo) (Asin.asin a.hi)
  else rejected

/-- An interval that contains the width `hi - lo` of an interval. -/
def widthI (a : Interval) : Interval := sub (point a.hi) (point a.lo)

/-- A status, the intervals of TRIAD's matrix row by row, and the error bound. -/
structure Estimate where
  status : UInt64
  m11 : Interval
  m12 : Interval
  m13 : Interval
  m21 : Interval
  m22 : Interval
  m23 : Interval
  m31 : Interval
  m32 : Interval
  m33 : Interval
  err : Float
  deriving Inhabited

/-- The intervals of `x` and `h` of the bound for the error bounds and the references. -/
def bdOf (inv half : Array UInt64) (e1 e2 r1x r1y r1z r2x r2y r2z : Float) : Interval × Interval :=
  Spec.boundOfI inv half inv inv (point e1) (point e2) (point r1x) (point r1y) (point r1z)
    (point r2x) (point r2y) (point r2z)

/-- The interval of `η`, the root of the sum of the squared widths of nine intervals. -/
def etaOf (m11 m12 m13 m21 m22 m23 m31 m32 m33 : Interval) : Interval :=
  let s1 := add (add (sq (widthI m11)) (sq (widthI m12))) (sq (widthI m13))
  let s2 := add (add (sq (widthI m21)) (sq (widthI m22))) (sq (widthI m23))
  let s3 := add (add (sq (widthI m31)) (sq (widthI m32))) (sq (widthI m33))
  sqrt (add (add s1 s2) s3)

/-- The interval of `2 arcsin √h + arcsin (η / (1 - η))`.  `h` lies in `[0, 1]`, and the clamp
removes the part of its interval below zero that outward rounding adds when `h` is zero. -/
def errOf (h eta : Interval) : Interval :=
  add (mul (ofInt 2) (asinI (sqrt (clamp h 0 1.0)))) (asinI (div eta (sub (ofInt 1) eta)))

/-- The status and the bound for the error bounds `e1` and `e2`, the references, and the
matrix's intervals: status 0 with the bound, or status 2 with zero. -/
def boundWith (inv half : Array UInt64) (e1 e2 r1x r1y r1z r2x r2y r2z : Float)
    (m11 m12 m13 m21 m22 m23 m31 m32 m33 : Interval) : UInt64 × Float :=
  let bd := bdOf inv half e1 e2 r1x r1y r1z r2x r2y r2z
  let d := add (point e1) (point e2)
  let eta := etaOf m11 m12 m13 m21 m22 m23 m31 m32 m33
  if 0 ≤ e1 && 0 ≤ e2 && d.status == 0 && bd.1.status == 0 && eta.status == 0 then
    if d.hi ≤ 1.5 && bd.1.hi < 1.0 && eta.hi ≤ 0.25 then
      let err := errOf bd.2 eta
      if err.status == 0 then (0, err.hi) else (2, 0.0)
    else (2, 0.0)
  else (2, 0.0)

/-- The estimate from the lengths and the matrix of `Spec.triadOf`. -/
def finishWith (inv half : Array UInt64) (e1 e2 r1x r1y r1z r2x r2y r2z : Float)
    (r : Interval × Interval × Interval × Interval × Interval × Interval × Interval × Interval ×
      Interval × Interval × Interval × Interval × Interval) : Estimate :=
  let nb := r.1
  let nbx := r.2.1
  let nr := r.2.2.1
  let nrx := r.2.2.2.1
  let m11 := r.2.2.2.2.1
  let m12 := r.2.2.2.2.2.1
  let m13 := r.2.2.2.2.2.2.1
  let m21 := r.2.2.2.2.2.2.2.1
  let m22 := r.2.2.2.2.2.2.2.2.1
  let m23 := r.2.2.2.2.2.2.2.2.2.1
  let m31 := r.2.2.2.2.2.2.2.2.2.2.1
  let m32 := r.2.2.2.2.2.2.2.2.2.2.2.1
  let m33 := r.2.2.2.2.2.2.2.2.2.2.2.2
  if nb.status == 0 && nbx.status == 0 && nr.status == 0 && nrx.status == 0 &&
      m11.status == 0 && m12.status == 0 && m13.status == 0 && m21.status == 0 &&
      m22.status == 0 && m23.status == 0 && m31.status == 0 && m32.status == 0 &&
      m33.status == 0 then
    if 0 < nb.lo && 0 < nbx.lo && 0 < nr.lo && 0 < nrx.lo then
      let b := boundWith inv half e1 e2 r1x r1y r1z r2x r2y r2z m11 m12 m13 m21 m22 m23 m31 m32 m33
      ⟨b.1, m11, m12, m13, m21, m22, m23, m31, m32, m33, b.2⟩
    else ⟨1, rejected, rejected, rejected, rejected, rejected, rejected, rejected, rejected,
      rejected, 0.0⟩
  else ⟨1, rejected, rejected, rejected, rejected, rejected, rejected, rejected, rejected,
    rejected, 0.0⟩

/-- TRIAD's matrix, which maps body coordinates to inertial coordinates, for the measurements
`b1`, `b2` and the references `r1`, `r2`, with the error bound for the bounds `e1`, `e2`. -/
def triadWith (inv half : Array UInt64)
    (b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2 : Float) : Estimate :=
  finishWith inv half e1 e2 r1x r1y r1z r2x r2y r2z
    (Spec.triadOfI inv half inv inv (point b1x) (point b1y) (point b1z) (point b2x) (point b2y)
      (point b2z) (point r1x) (point r1y) (point r1z) (point r2x) (point r2y) (point r2z))

def triad (b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2 : Float) : Estimate :=
  triadWith Trig.invPi Trig.halfPi b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2

end Demos.Attitude
