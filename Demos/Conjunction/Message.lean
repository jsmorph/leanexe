import Demos.Conjunction.Box
import Library.Numerics.Interval.Enclose

/-!
The conjunction-message form.  A conjunction data message (CCSDS 508.0-B-1) gives each object's
position in km and velocity in km/s in one inertial frame, and its position covariance in m² in the
object's RTN frame.  `encounter` defines from these the miss vector and its covariance in the
encounter plane, and `enclosure_def` declares with it the interval program `encounterI` and the
theorem `encounter.encloses`.  `pcMessageWith` evaluates `encounterI` on the inputs and passes
the intervals to `pcTail` through `setupBox`, and `assessMessageWith` compares the result with a
threshold.  The interval functions take four tables that they do not use, for the `sin`, `cos`,
and `pow` of `enclosure_def`, and `encounterAt` passes the table of `exp` for each.  `pcMessage`
and `assessMessage` pass the tables of `exp` and `erfc`.
-/

namespace Demos.Conjunction

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-- The unit vectors `R̂ = r/|r|`, `T̂ = N̂ × R̂`, and `N̂ = (r × v)/|r × v|` of the RTN frame of
the state with position `r = (px, py, pz)` and velocity `v = (vx, vy, vz)`, in the inertial frame:
the components of `R̂`, then of `T̂`, then of `N̂`. -/
enclosure_def rtnAxes (px py pz vx vy vz) :=
  let rn := √(px * px + py * py + pz * pz)
  let hx := py * vz - pz * vy
  let hy := pz * vx - px * vz
  let hz := px * vy - py * vx
  let hn := √(hx * hx + hy * hy + hz * hz)
  let a1 := px / rn
  let a2 := py / rn
  let a3 := pz / rn
  let c1 := hx / hn
  let c2 := hy / hn
  let c3 := hz / hn
  (a1, a2, a3, c2 * a3 - c3 * a2, c3 * a1 - c1 * a3, c1 * a2 - c2 * a1, c1, c2, c3)

/-- The product `C b` of the symmetric matrix `C` with the entries `xx`, `xy`, `xz`, `yy`, `yz`,
and `zz` and the vector `b`. -/
enclosure_def symMul (cxx cxy cxz cyy cyz czz b1 b2 b3) :=
  (cxx * b1 + cxy * b2 + cxz * b3, cxy * b1 + cyy * b2 + cyz * b3,
    cxz * b1 + cyz * b2 + czz * b3)

/-- The bilinear form `aᵀ C b` of the symmetric matrix `C` of `symMul`. -/
enclosure_def bilinear (cxx cxy cxz cyy cyz czz a1 a2 a3 b1 b2 b3) :=
  let (p1, p2, p3) := symMul cxx cxy cxz cyy cyz czz b1 b2 b3
  a1 * p1 + a2 * p2 + a3 * p3

/-- The covariance `Q C Qᵀ` in the inertial frame of the covariance `C` given in the frame whose
axes are `R̂ = (r1, r2, r3)`, `T̂ = (t1, t2, t3)`, and `N̂ = (n1, n2, n3)`, the columns of `Q`.
`C` has the entries `crr`, `ctr`, `ctt`, `cnr`, `cnt`, and `cnn`, and the result holds the entries
`xx`, `xy`, `xz`, `yy`, `yz`, and `zz`.  Entry `ij` is `qᵢᵀ C qⱼ`, where `qᵢ = (rᵢ, tᵢ, nᵢ)` is row
`i` of `Q`. -/
enclosure_def rtnToInertial (r1 r2 r3 t1 t2 t3 n1 n2 n3 crr ctr ctt cnr cnt cnn) :=
  (bilinear crr ctr cnr ctt cnt cnn r1 t1 n1 r1 t1 n1,
    bilinear crr ctr cnr ctt cnt cnn r1 t1 n1 r2 t2 n2,
    bilinear crr ctr cnr ctt cnt cnn r1 t1 n1 r3 t3 n3,
    bilinear crr ctr cnr ctt cnt cnn r2 t2 n2 r2 t2 n2,
    bilinear crr ctr cnr ctt cnt cnn r2 t2 n2 r3 t3 n3,
    bilinear crr ctr cnr ctt cnt cnn r3 t3 n3 r3 t3 n3)

/-- The axes of the encounter plane for the relative position `d` and the relative velocity `u`:
`ẑ = u/|u|`, `x̂` along `d - (d · ẑ) ẑ`, the part of `d` perpendicular to `ẑ`, and `ŷ = ẑ × x̂`,
as the components of `x̂` and then of `ŷ`. -/
enclosure_def planeAxes (d1 d2 d3 u1 u2 u3) :=
  let un := √(u1 * u1 + u2 * u2 + u3 * u3)
  let z1 := u1 / un
  let z2 := u2 / un
  let z3 := u3 / un
  let dz := d1 * z1 + d2 * z2 + d3 * z3
  let a1 := d1 - dz * z1
  let a2 := d2 - dz * z2
  let a3 := d3 - dz * z3
  let an := √(a1 * a1 + a2 * a2 + a3 * a3)
  let e1 := a1 / an
  let e2 := a2 / an
  let e3 := a3 / an
  (e1, e2, e3, z2 * e3 - z3 * e2, z3 * e1 - z1 * e3, z1 * e2 - z2 * e1)

/-- The miss vector `(m1, m2)` in m and its covariance `(c11, c12, c22)` in m² in the encounter
plane of two objects, from each object's position `(x, y, z)` in km and velocity `(vx, vy, vz)` in
km/s in one inertial frame and its position covariance in m² in its RTN frame, with the entries in
the message's order `CR_R`, `CT_R`, `CT_T`, `CN_R`, `CN_T`, `CN_N`.  The relative position is
`Δr = 1000 (r₂ - r₁)` in m and the relative velocity `Δv = v₂ - v₁`, the covariance `C` is the sum
of the two covariances in the inertial frame, and `x̂` and `ŷ` are the axes of `planeAxes` for
`Δr` and `Δv`.  The miss vector is `(Δr · x̂, Δr · ŷ)`, and the covariance has the entries
`x̂ᵀ C x̂`, `x̂ᵀ C ŷ`, and `ŷᵀ C ŷ`. -/
enclosure_def encounter (x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2
    crr2 ctr2 ctt2 cnr2 cnt2 cnn2) :=
  let (a1, a2, a3, b1, b2, b3, c1, c2, c3) := rtnAxes x1 y1 z1 vx1 vy1 vz1
  let (f1, f2, f3, g1, g2, g3, h1, h2, h3) := rtnAxes x2 y2 z2 vx2 vy2 vz2
  let (pxx, pxy, pxz, pyy, pyz, pzz) :=
    rtnToInertial a1 a2 a3 b1 b2 b3 c1 c2 c3 crr1 ctr1 ctt1 cnr1 cnt1 cnn1
  let (qxx, qxy, qxz, qyy, qyz, qzz) :=
    rtnToInertial f1 f2 f3 g1 g2 g3 h1 h2 h3 crr2 ctr2 ctt2 cnr2 cnt2 cnn2
  let cxx := pxx + qxx
  let cxy := pxy + qxy
  let cxz := pxz + qxz
  let cyy := pyy + qyy
  let cyz := pyz + qyz
  let czz := pzz + qzz
  let d1 := 1000 * (x2 - x1)
  let d2 := 1000 * (y2 - y1)
  let d3 := 1000 * (z2 - z1)
  let (e1, e2, e3, k1, k2, k3) := planeAxes d1 d2 d3 (vx2 - vx1) (vy2 - vy1) (vz2 - vz1)
  (d1 * e1 + d2 * e2 + d3 * e3, d1 * k1 + d2 * k2 + d3 * k3,
    bilinear cxx cxy cxz cyy cyz czz e1 e2 e3 e1 e2 e3,
    bilinear cxx cxy cxz cyy cyz czz e1 e2 e3 k1 k2 k3,
    bilinear cxx cxy cxz cyy cyz czz k1 k2 k3 k1 k2 k3)

/-- The intervals of `encounterI` for the inputs as points. -/
def encounterAt (tab : Array UInt64) (x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2
    vx2 vy2 vz2 crr2 ctr2 ctt2 cnr2 cnt2 cnn2 : Float) :
    Interval × Interval × Interval × Interval × Interval :=
  encounterI tab tab tab tab (point x1) (point y1) (point z1) (point vx1) (point vy1) (point vz1)
    (point crr1) (point ctr1) (point ctt1) (point cnr1) (point cnt1) (point cnn1) (point x2)
    (point y2) (point z2) (point vx2) (point vy2) (point vz2) (point crr2) (point ctr2)
    (point ctt2) (point cnr2) (point cnt2) (point cnn2)

/-- An interval that contains the probability of collision of the encounter that `encounter`
defines from the inputs, for the radius `r` in m, from `n` panels. -/
def pcMessageWith (tab fastT accT cexpT asymT asymAccT expAccT excT : Array UInt64)
    (x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2 ctr2 ctt2 cnr2
      cnt2 cnn2 r : Float) (n : UInt64) : Interval :=
  let e := encounterAt tab x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2
    crr2 ctr2 ctt2 cnr2 cnt2 cnn2
  pcTail tab fastT accT cexpT asymT asymAccT expAccT excT
    (setupBox e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 r) e.2.2.1 r n

def assessMessageWith (tab fastT accT cexpT asymT asymAccT expAccT excT : Array UInt64)
    (x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2 ctr2 ctt2 cnr2
      cnt2 cnn2 r t : Float) (n : UInt64) : Assessment :=
  judge (pcMessageWith tab fastT accT cexpT asymT asymAccT expAccT excT x1 y1 z1 vx1 vy1 vz1 crr1
    ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2 ctr2 ctt2 cnr2 cnt2 cnn2 r n) t

def pcMessage (x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2 ctr2
    ctt2 cnr2 cnt2 cnn2 r : Float) (n : UInt64) : Interval :=
  pcMessageWith Exp.expTable Erfc.fastTable Erfc.accTable Erfc.expTable Erfc.asymTable
    Erfc.asymAccTable Erfc.expAccTable Erfc.excTable x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1
    cnn1 x2 y2 z2 vx2 vy2 vz2 crr2 ctr2 ctt2 cnr2 cnt2 cnn2 r n

def assessMessage (x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1 cnn1 x2 y2 z2 vx2 vy2 vz2 crr2
    ctr2 ctt2 cnr2 cnt2 cnn2 r t : Float) (n : UInt64) : Assessment :=
  assessMessageWith Exp.expTable Erfc.fastTable Erfc.accTable Erfc.expTable Erfc.asymTable
    Erfc.asymAccTable Erfc.expAccTable Erfc.excTable x1 y1 z1 vx1 vy1 vz1 crr1 ctr1 ctt1 cnr1 cnt1
    cnn1 x2 y2 z2 vx2 vy2 vz2 crr2 ctr2 ctt2 cnr2 cnt2 cnn2 r t n

end Demos.Conjunction
