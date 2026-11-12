import Demos.Attitude.QSpec
import Demos.Attitude.Program
import LeanExe.Dialect.Loop

/-!
The q-method with a certified error bound.  `qmethodWith` reads `n` observations, each a
measurement `b`, a reference `r`, a weight `a`, and an error bound `ε`, encloses Davenport's
matrix `K` of the normalized vectors in intervals (`accumulate`), and finds an eigenpair of the
midpoint matrix with eight cyclic Jacobi sweeps (`jacobi`), which no theorem concerns.  From the
two largest eigenvalue estimates `λ̂1 ≥ λ̂2` it takes the cut `c = λ̂2 + (λ̂1 - λ̂2) / 16`, and
`certify` encloses the pivots of the factorization of `K - c I` that takes the diagonal entry of
largest magnitude first at each stage, the Rayleigh quotient and residual of the computed
quaternion `q̂`, and the two bounds.  The squared residual is not negative, and the clamp before
its square root removes the part of its interval below zero that outward rounding adds when the
residual's interval reaches zero.  `QSoundness.lean` states what a result of status 0 implies.

| Status | Meaning |
|---|---|
| 0 | The pivots certify the cut, and `errOpt` and `err` bound the angles to the optimal and to every true attitude. |
| 1 | The input fails its conditions, or an interval of `K`, of a length, or of the two sums rejects. |
| 2 | The certificate failed: a pivot, a gap, or an arcsine is rejected or has the wrong sign. |
-/

namespace Demos.Attitude.QMethod

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-- The intervals of a symmetric 4×4 matrix, by its entries on and above the diagonal. -/
structure M4 where
  a00 : Interval
  a01 : Interval
  a02 : Interval
  a03 : Interval
  a11 : Interval
  a12 : Interval
  a13 : Interval
  a22 : Interval
  a23 : Interval
  a33 : Interval
  deriving Inhabited

/-- The intervals of a symmetric 3×3 matrix. -/
structure M3 where
  c00 : Interval
  c01 : Interval
  c02 : Interval
  c11 : Interval
  c12 : Interval
  c22 : Interval
  deriving Inhabited

/-- The intervals of a symmetric 2×2 matrix. -/
structure M2 where
  d00 : Interval
  d01 : Interval
  d11 : Interval
  deriving Inhabited

/-- The state of the accumulation: whether every length so far has a positive lower endpoint, the
intervals of Davenport's matrix, and the intervals of `Σ a sin ε` and `Σ a cos ε`. -/
structure Acc where
  ok : Bool
  k : M4
  rho : Interval
  mu : Interval
  deriving Inhabited

/-- A quaternion of floats, or a column of the Jacobi rotations. -/
structure Q4 where
  w : Float
  x : Float
  y : Float
  z : Float
  deriving Inhabited

/-- The state of the Jacobi sweeps: the entries of the matrix on and above the diagonal, and the
columns of the accumulated rotation. -/
structure Jac where
  a00 : Float
  a01 : Float
  a02 : Float
  a03 : Float
  a11 : Float
  a12 : Float
  a13 : Float
  a22 : Float
  a23 : Float
  a33 : Float
  v0 : Q4
  v1 : Q4
  v2 : Q4
  v3 : Q4
  deriving Inhabited

def rd (xs : Array Float) (i : UInt64) : Float := xs[i.toNat]!

/-! ### Input -/

/-- `x` is a whole number from `lo` to `hi`. -/
def isWhole (x : Float) (lo hi : UInt64) : Bool :=
  let n := x.toUInt64
  n.toFloat == x && lo ≤ n && n ≤ hi

def allFinite (xs : Array Float) : Bool :=
  LeanExe.loop xs.size.toUInt64 true fun i ok => ok && finite (rd xs i)

/-- The record at index `b` has a positive weight and an error bound in `[0, 1.5]`. -/
def recordOk (xs : Array Float) (b : UInt64) : Bool :=
  0 < rd xs (b + 6) && 0 ≤ rd xs (b + 7) && rd xs (b + 7) ≤ 1.5

/-- The input meets the conditions of `requirements.md`. -/
def valid (xs : Array Float) : Bool :=
  isWhole (rd xs 0) 2 16 && xs.size.toUInt64 == 1 + 8 * (rd xs 0).toUInt64 && allFinite xs &&
    LeanExe.loop (rd xs 0).toUInt64 true fun i ok => ok && recordOk xs (1 + 8 * i)

/-! ### Davenport's matrix -/

/-- The accumulation after the observation at index `b`. -/
def addObs (inv half : Array UInt64) (xs : Array Float) (b : UInt64) (s : Acc) : Acc :=
  let b1 := point (rd xs b)
  let b2 := point (rd xs (b + 1))
  let b3 := point (rd xs (b + 2))
  let r1 := point (rd xs (b + 3))
  let r2 := point (rd xs (b + 4))
  let r3 := point (rd xs (b + 5))
  let sc := Spec.obsScaleI inv half inv inv b1 b2 b3 r1 r2 r3 (point (rd xs (b + 6)))
  let f := Spec.obsFirstI inv half inv inv b1 b2 b3 r1 r2 r3 sc.2.2
  let g := Spec.obsRestI inv half inv inv b1 b2 b3 r1 r2 r3 sc.2.2 f.1
  let t := Spec.obsTrueI inv half inv inv (point (rd xs (b + 6))) (point (rd xs (b + 7)))
  ⟨s.ok && sc.1.status == 0 && 0 < sc.1.lo && sc.2.1.status == 0 && 0 < sc.2.1.lo,
    ⟨add s.k.a00 f.1, add s.k.a01 f.2.1, add s.k.a02 f.2.2.1, add s.k.a03 f.2.2.2,
      add s.k.a11 g.1, add s.k.a12 g.2.1, add s.k.a13 g.2.2.1, add s.k.a22 g.2.2.2.1,
      add s.k.a23 g.2.2.2.2.1, add s.k.a33 g.2.2.2.2.2⟩,
    add s.rho t.1, add s.mu t.2⟩

def zeroI : Interval := point 0

/-- The accumulation over the first `n` observations. -/
def accumulate (inv half : Array UInt64) (xs : Array Float) (n : UInt64) : Acc :=
  LeanExe.loop n ⟨true, ⟨zeroI, zeroI, zeroI, zeroI, zeroI, zeroI, zeroI, zeroI, zeroI, zeroI⟩,
    zeroI, zeroI⟩ fun i s => addObs inv half xs (1 + 8 * i) s

/-- Every interval of the accumulation is accepted, and every length has a positive lower
endpoint. -/
def accepted (s : Acc) : Bool :=
  s.ok && s.k.a00.status == 0 && s.k.a01.status == 0 && s.k.a02.status == 0 &&
    s.k.a03.status == 0 && s.k.a11.status == 0 && s.k.a12.status == 0 && s.k.a13.status == 0 &&
    s.k.a22.status == 0 && s.k.a23.status == 0 && s.k.a33.status == 0 && s.rho.status == 0 &&
    s.mu.status == 0

/-! ### The Jacobi sweeps -/

/-- The cosine, sine, and tangent of the rotation that annihilates `apq`. -/
def rotCS (app aqq apq : Float) : Float × Float × Float :=
  if apq == 0 then (1.0, 0.0, 0.0)
  else
    let th := (aqq - app) / (2.0 * apq)
    let t := (if th < 0 then -1.0 else 1.0) / (Float.abs th + Float.sqrt (th * th + 1.0))
    let c := 1.0 / Float.sqrt (t * t + 1.0)
    (c, t * c, t)

/-- The columns `c u - s v` and `s u + c v`. -/
def mixL (c s : Float) (u v : Q4) : Q4 :=
  ⟨c * u.w - s * v.w, c * u.x - s * v.x, c * u.y - s * v.y, c * u.z - s * v.z⟩

def mixR (c s : Float) (u v : Q4) : Q4 :=
  ⟨s * u.w + c * v.w, s * u.x + c * v.x, s * u.y + c * v.y, s * u.z + c * v.z⟩

def rot01 (j : Jac) : Jac :=
  let r := rotCS j.a00 j.a11 j.a01
  let c := r.1
  let s := r.2.1
  let t := r.2.2
  { j with
    a00 := j.a00 - t * j.a01, a11 := j.a11 + t * j.a01, a01 := 0.0,
    a02 := c * j.a02 - s * j.a12, a12 := s * j.a02 + c * j.a12,
    a03 := c * j.a03 - s * j.a13, a13 := s * j.a03 + c * j.a13,
    v0 := mixL c s j.v0 j.v1, v1 := mixR c s j.v0 j.v1 }

def rot02 (j : Jac) : Jac :=
  let r := rotCS j.a00 j.a22 j.a02
  let c := r.1
  let s := r.2.1
  let t := r.2.2
  { j with
    a00 := j.a00 - t * j.a02, a22 := j.a22 + t * j.a02, a02 := 0.0,
    a01 := c * j.a01 - s * j.a12, a12 := s * j.a01 + c * j.a12,
    a03 := c * j.a03 - s * j.a23, a23 := s * j.a03 + c * j.a23,
    v0 := mixL c s j.v0 j.v2, v2 := mixR c s j.v0 j.v2 }

def rot03 (j : Jac) : Jac :=
  let r := rotCS j.a00 j.a33 j.a03
  let c := r.1
  let s := r.2.1
  let t := r.2.2
  { j with
    a00 := j.a00 - t * j.a03, a33 := j.a33 + t * j.a03, a03 := 0.0,
    a01 := c * j.a01 - s * j.a13, a13 := s * j.a01 + c * j.a13,
    a02 := c * j.a02 - s * j.a23, a23 := s * j.a02 + c * j.a23,
    v0 := mixL c s j.v0 j.v3, v3 := mixR c s j.v0 j.v3 }

def rot12 (j : Jac) : Jac :=
  let r := rotCS j.a11 j.a22 j.a12
  let c := r.1
  let s := r.2.1
  let t := r.2.2
  { j with
    a11 := j.a11 - t * j.a12, a22 := j.a22 + t * j.a12, a12 := 0.0,
    a01 := c * j.a01 - s * j.a02, a02 := s * j.a01 + c * j.a02,
    a13 := c * j.a13 - s * j.a23, a23 := s * j.a13 + c * j.a23,
    v1 := mixL c s j.v1 j.v2, v2 := mixR c s j.v1 j.v2 }

def rot13 (j : Jac) : Jac :=
  let r := rotCS j.a11 j.a33 j.a13
  let c := r.1
  let s := r.2.1
  let t := r.2.2
  { j with
    a11 := j.a11 - t * j.a13, a33 := j.a33 + t * j.a13, a13 := 0.0,
    a01 := c * j.a01 - s * j.a03, a03 := s * j.a01 + c * j.a03,
    a12 := c * j.a12 - s * j.a23, a23 := s * j.a12 + c * j.a23,
    v1 := mixL c s j.v1 j.v3, v3 := mixR c s j.v1 j.v3 }

def rot23 (j : Jac) : Jac :=
  let r := rotCS j.a22 j.a33 j.a23
  let c := r.1
  let s := r.2.1
  let t := r.2.2
  { j with
    a22 := j.a22 - t * j.a23, a33 := j.a33 + t * j.a23, a23 := 0.0,
    a02 := c * j.a02 - s * j.a03, a03 := s * j.a02 + c * j.a03,
    a12 := c * j.a12 - s * j.a13, a13 := s * j.a12 + c * j.a13,
    v2 := mixL c s j.v2 j.v3, v3 := mixR c s j.v2 j.v3 }

/-- One cyclic sweep over the six pairs of indices. -/
def sweep (j : Jac) : Jac := rot23 (rot13 (rot12 (rot03 (rot02 (rot01 j)))))

/-- Eight sweeps from the midpoints of the intervals of `K`, with the identity as the rotation. -/
def jacobi (k : M4) : Jac :=
  LeanExe.loop 8 ⟨mid k.a00, mid k.a01, mid k.a02, mid k.a03, mid k.a11, mid k.a12, mid k.a13,
    mid k.a22, mid k.a23, mid k.a33, ⟨1.0, 0.0, 0.0, 0.0⟩, ⟨0.0, 1.0, 0.0, 0.0⟩,
    ⟨0.0, 0.0, 1.0, 0.0⟩, ⟨0.0, 0.0, 0.0, 1.0⟩⟩ fun _ j => sweep j

/-- The index of the largest of four values, the first on ties. -/
def top4 (d0 d1 d2 d3 : Float) : UInt64 :=
  if d0 ≥ d1 && d0 ≥ d2 && d0 ≥ d3 then 0
  else if d1 ≥ d2 && d1 ≥ d3 then 1
  else if d2 ≥ d3 then 2
  else 3

/-- The value at index `i` and the largest of the other three. -/
def pick (i : UInt64) (d0 d1 d2 d3 : Float) : Float × Float :=
  if i == 0 then (d0, max d1 (max d2 d3))
  else if i == 1 then (d1, max d0 (max d2 d3))
  else if i == 2 then (d2, max d0 (max d1 d3))
  else (d3, max d0 (max d1 d2))

def column (i : UInt64) (j : Jac) : Q4 :=
  if i == 0 then j.v0 else if i == 1 then j.v1 else if i == 2 then j.v2 else j.v3

/-- `q` scaled to unit length, with a scalar part that is not negative. -/
def normalize (q : Q4) : Q4 :=
  let n := Float.sqrt (q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z)
  let k := if q.w < 0 then -1.0 / n else 1.0 / n
  ⟨k * q.w, k * q.x, k * q.y, k * q.z⟩

/-! ### The certificate -/

/-- `A - c I`. -/
def shiftI (A : M4) (c : Interval) : M4 :=
  { A with
    a00 := sub A.a00 c, a11 := sub A.a11 c, a22 := sub A.a22 c, a33 := sub A.a33 c }

/-- The larger magnitude of the endpoints of an interval. -/
def mag (a : Interval) : Float := max (Float.abs a.lo) (Float.abs a.hi)

/-- `A` with the indices 0 and `p` exchanged, for `p` from 1 to 3. -/
def swap4 (p : UInt64) (A : M4) : M4 :=
  if p == 1 then ⟨A.a11, A.a01, A.a12, A.a13, A.a00, A.a02, A.a03, A.a22, A.a23, A.a33⟩
  else if p == 2 then ⟨A.a22, A.a12, A.a02, A.a23, A.a11, A.a01, A.a13, A.a00, A.a03, A.a33⟩
  else if p == 3 then ⟨A.a33, A.a13, A.a23, A.a03, A.a11, A.a12, A.a01, A.a22, A.a02, A.a00⟩
  else A

def swap3 (p : UInt64) (B : M3) : M3 :=
  if p == 1 then ⟨B.c11, B.c01, B.c12, B.c00, B.c02, B.c22⟩
  else if p == 2 then ⟨B.c22, B.c12, B.c02, B.c11, B.c01, B.c00⟩
  else B

def swap2 (p : UInt64) (C : M2) : M2 := if p == 1 then ⟨C.d11, C.d01, C.d00⟩ else C

/-- The first stage: the pivot and the Schur complement of `A` after the diagonal entry of largest
magnitude moves to the front. -/
def stage4 (inv half : Array UInt64) (A : M4) : Interval × M3 :=
  let A' := swap4 (top4 (mag A.a00) (mag A.a11) (mag A.a22) (mag A.a33)) A
  let s := Spec.schur4I inv half inv inv A'.a00 A'.a01 A'.a02 A'.a03 A'.a11 A'.a12 A'.a13 A'.a22
    A'.a23 A'.a33
  (A'.a00, ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2⟩)

def stage3 (inv half : Array UInt64) (B : M3) : Interval × M2 :=
  let m0 := mag B.c00
  let m1 := mag B.c11
  let m2 := mag B.c22
  let B' := swap3 (if m0 ≥ m1 && m0 ≥ m2 then 0 else if m1 ≥ m2 then 1 else 2) B
  let s := Spec.schur3I inv half inv inv B'.c00 B'.c01 B'.c02 B'.c11 B'.c12 B'.c22
  (B'.c00, ⟨s.1, s.2.1, s.2.2⟩)

def stage2 (inv half : Array UInt64) (C : M2) : Interval × Interval :=
  let C' := swap2 (if mag C.d00 ≥ mag C.d11 then 0 else 1) C
  (C'.d00, Spec.schur2I inv half inv inv C'.d00 C'.d01 C'.d11)

/-- The four pivots of the factorization with the largest diagonal magnitude first. -/
def pivotsI (inv half : Array UInt64) (A : M4) : Interval × Interval × Interval × Interval :=
  let s4 := stage4 inv half A
  let s3 := stage3 inv half s4.2
  let s2 := stage2 inv half s3.2
  (s4.1, s3.1, s2.1, s2.2)

def isPos (a : Interval) : Bool := a.status == 0 && 0 < a.lo

def isNeg (a : Interval) : Bool := a.status == 0 && a.hi < 0

/-- One pivot is positive and the other three negative. -/
def signsOk (d : Interval × Interval × Interval × Interval) : Bool :=
  (isPos d.1 && isNeg d.2.1 && isNeg d.2.2.1 && isNeg d.2.2.2) ||
    (isNeg d.1 && isPos d.2.1 && isNeg d.2.2.1 && isNeg d.2.2.2) ||
    (isNeg d.1 && isNeg d.2.1 && isPos d.2.2.1 && isNeg d.2.2.2) ||
    (isNeg d.1 && isNeg d.2.1 && isNeg d.2.2.1 && isPos d.2.2.2)

/-- The rejected result of a status. -/
def rejectWith (status : Float) : Array Float := #[status, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]

/-- The certificate for the intervals `K` of Davenport's matrix, `rt` and `mt` of
`Σ a sin ε` and `Σ a cos ε`, the cut `c`, and the quaternion `q`: status 0 with `q`, `errOpt`,
`err`, and `c`, or status 2. -/
def certify (inv half : Array UInt64) (K : M4) (rt mt : Interval) (c : Float) (q : Q4) :
    Array Float :=
  let d := pivotsI inv half (shiftI K (point c))
  let u := Spec.applyKI inv half inv inv K.a00 K.a01 K.a02 K.a03 K.a11 K.a12 K.a13 K.a22 K.a23
    K.a33 (point q.w) (point q.x) (point q.y) (point q.z)
  let r := Spec.residOfI inv half inv inv u.1 u.2.1 u.2.2.1 u.2.2.2 (point q.w) (point q.x)
    (point q.y) (point q.z)
  let b := Spec.boundsOfI inv half inv inv r.2.1 (sqrt (clamp r.2.2 0 r.2.2.hi)) rt mt (point c)
  let s := asinI b.2.2.1
  let eo := mul (ofInt 2) s
  let e := mul (ofInt 2) (add s (asinI b.2.2.2))
  if signsOk d && r.1.status == 0 && 0 < r.1.lo && b.1.status == 0 && 0 < b.1.lo &&
      b.2.1.status == 0 && 0 < b.2.1.lo && eo.status == 0 && e.status == 0 then
    #[0.0, q.w, q.x, q.y, q.z, eo.hi, e.hi, c]
  else rejectWith 2.0

/-- The q-method on the input `xs`, with the tables of `sin` and `cos`. -/
def qmethodWith (inv half : Array UInt64) (xs : Array Float) : Array Float :=
  if valid xs then
    let s := accumulate inv half xs (rd xs 0).toUInt64
    if accepted s then
      let j := jacobi s.k
      let i := top4 j.a00 j.a11 j.a22 j.a33
      let l := pick i j.a00 j.a11 j.a22 j.a33
      certify inv half s.k s.rho s.mu (l.2 + (l.1 - l.2) / 16.0) (normalize (column i j))
    else rejectWith 1.0
  else rejectWith 1.0

def qmethod (xs : Array Float) : Array Float := qmethodWith Trig.invPi Trig.halfPi xs

end Demos.Attitude.QMethod
