import Library.Numerics.Interval.Enclose
import Demos.Avoidance.KeplerRoot

/-!
The model of the authorizer, stated once for the real numbers and for intervals.  Each
`enclosure_def` declares a real function, the interval function `fI` that the program runs, and
the theorem `f.encloses`.  `propagate` is the two-body state `t` seconds after a state, by the
Lagrange coefficients `f` and `g` in the change of the eccentric anomaly.  `shape` gives the
inverse of the semimajor axis and the square of the eccentricity of a state, `plane` the miss
vector and the projected covariance in the encounter plane, and `after`, the model's definition,
the encounter after a burn.  The program evaluates `relative`, `shape`,
`axes`, and `project`, which computes the projected covariance in a form centered at points near
the axes.  `project_eq` in `Geometry.lean` states that the centered form equals the plain
projection, and `after_eq_plain` in `Soundness.lean` writes `after` through `axes`.
-/

open Real

namespace Demos.Avoidance

/-- The position in km and the velocity in km/s `t` seconds after the state `(r, v)`, for the
gravitational parameter `mu` in km³/s². -/
enclosure_def propagate (mu rx ry rz vx vy vz t) :=
  let r0 := √(rx * rx + ry * ry + rz * rz)
  let d := rx * vx + ry * vy + rz * vz
  let v2 := vx * vx + vy * vy + vz * vz
  let alpha := 2 / r0 - v2 / mu
  let q := √(alpha / mu)
  let n := mu * alpha * q
  let ak := 1 - r0 * alpha
  let bk := -(d * q)
  let E := keplerRoot ak bk (n * t + bk)
  let c := cos E
  let s := sin E
  let w := 1 - ak * c - bk * s
  let f := 1 - (1 - c) / (r0 * alpha)
  let g := (r0 * alpha * s + d * q * (1 - c)) / n
  let fd := -(alpha * s) / (q * w * r0)
  let gd := 1 - (1 - c) / w
  (f * rx + g * vx, f * ry + g * vy, f * rz + g * vz, fd * rx + gd * vx, fd * ry + gd * vy,
    fd * rz + gd * vz)

/-- The inverse `α` of the semimajor axis and the square `a_k² + b_k²` of the eccentricity of the
state `(r, v)`. -/
enclosure_def shape (mu rx ry rz vx vy vz) :=
  let r0 := √(rx * rx + ry * ry + rz * rz)
  let d := rx * vx + ry * vy + rz * vz
  let v2 := vx * vx + vy * vy + vz * vz
  let alpha := 2 / r0 - v2 / mu
  let q := √(alpha / mu)
  let ak := 1 - r0 * alpha
  let bk := -(d * q)
  (alpha, ak * ak + bk * bk)

/-- The miss vector `(ρ · x̂, ρ · ŷ)` and the covariance `C` projected on `x̂` and `ŷ`, for the
relative position `ρ = (px, py, pz)`, the relative velocity `ν = (ux, uy, uz)`, and the primary's
position `w`, with `x̂` along `w × ν`, `ẑ` along `ν`, and `ŷ = ẑ × x̂`, followed by
`|w × ν|²` and `|ν|²`. -/
enclosure_def plane (px py pz ux uy uz wx wy wz cxx cxy cxz cyy cyz czz) :=
  let xx := wy * uz - wz * uy
  let xy := wz * ux - wx * uz
  let xz := wx * uy - wy * ux
  let xn2 := xx * xx + xy * xy + xz * xz
  let zn2 := ux * ux + uy * uy + uz * uz
  let xn := √xn2
  let zn := √zn2
  let ex := xx / xn
  let ey := xy / xn
  let ez := xz / xn
  let kx := ux / zn
  let ky := uy / zn
  let kz := uz / zn
  let fx := ky * ez - kz * ey
  let fy := kz * ex - kx * ez
  let fz := kx * ey - ky * ex
  let cex := cxx * ex + cxy * ey + cxz * ez
  let cey := cxy * ex + cyy * ey + cyz * ez
  let cez := cxz * ex + cyz * ey + czz * ez
  let cfx := cxx * fx + cxy * fy + cxz * fz
  let cfy := cxy * fx + cyy * fy + cyz * fz
  let cfz := cxz * fx + cyz * fy + czz * fz
  (px * ex + py * ey + pz * ez, px * fx + py * fy + pz * fz, ex * cex + ey * cey + ez * cez,
    ex * cfx + ey * cfy + ez * cfz, fx * cfx + fy * cfy + fz * cfz, xn2, zn2)

/-- The axes of the encounter plane for the relative velocity `ν = (ux, uy, uz)` and the primary's
position `w`: `x̂` along `w × ν`, and `ŷ = ẑ × x̂` with `ẑ` along `ν`, followed by `|w × ν|²` and
`|ν|²`. -/
enclosure_def axes (ux uy uz wx wy wz) :=
  let xx := wy * uz - wz * uy
  let xy := wz * ux - wx * uz
  let xz := wx * uy - wy * ux
  let xn2 := xx * xx + xy * xy + xz * xz
  let zn2 := ux * ux + uy * uy + uz * uz
  let xn := √xn2
  let zn := √zn2
  let ex := xx / xn
  let ey := xy / xn
  let ez := xz / xn
  let kx := ux / zn
  let ky := uy / zn
  let kz := uz / zn
  (ex, ey, ez, ky * ez - kz * ey, kz * ex - kx * ez, kx * ey - ky * ex, xn2, zn2)

/-- The miss vector `(ρ · e, ρ · f)` and the covariance `C` projected on the axes `e` and `f`, in
the form centered at the vectors `g` and `h`: `eᵀCe = gᵀCg + 2 (e - g)ᵀCg + (e - g)ᵀC(e - g)`, and
alike for `eᵀCf` and `fᵀCf`.  The value does not depend on `g` and `h` (`project_eq`), and a `g`
near `e` keeps the large variances of `C` out of the width of the interval evaluation. -/
enclosure_def project (px py pz ex ey ez fx fy fz gx gy gz hx hy hz cxx cxy cxz cyy cyz czz) :=
  let dex := ex - gx
  let dey := ey - gy
  let dez := ez - gz
  let dfx := fx - hx
  let dfy := fy - hy
  let dfz := fz - hz
  let cgx := cxx * gx + cxy * gy + cxz * gz
  let cgy := cxy * gx + cyy * gy + cyz * gz
  let cgz := cxz * gx + cyz * gy + czz * gz
  let chx := cxx * hx + cxy * hy + cxz * hz
  let chy := cxy * hx + cyy * hy + cyz * hz
  let chz := cxz * hx + cyz * hy + czz * hz
  let cex := cxx * dex + cxy * dey + cxz * dez
  let cey := cxy * dex + cyy * dey + cyz * dez
  let cez := cxz * dex + cyz * dey + czz * dez
  let cfx := cxx * dfx + cxy * dfy + cxz * dfz
  let cfy := cxy * dfx + cyy * dfy + cyz * dfz
  let cfz := cxz * dfx + cyz * dfy + czz * dfz
  (px * ex + py * ey + pz * ez, px * fx + py * fy + pz * fz,
    gx * cgx + gy * cgy + gz * cgz + 2 * (dex * cgx + dey * cgy + dez * cgz) +
      (dex * cex + dey * cey + dez * cez),
    gx * chx + gy * chy + gz * chz + (dex * chx + dey * chy + dez * chz) +
      (dfx * cgx + dfy * cgy + dfz * cgz) + (dex * cfx + dey * cfy + dez * cfz),
    hx * chx + hy * chy + hz * chz + 2 * (dfx * chx + dfy * chy + dfz * chz) +
      (dfx * cfx + dfy * cfy + dfz * cfz))

/-- The relative position and velocity at the reference time after the burn `dv`: the nominal
relative state `r1 - r2`, `v1 - v2`, plus the change that the burn makes to the two-body
trajectory from the burn's state `(rb, vb)` over `dt` seconds, plus the displacement `d`. -/
enclosure_def relative (mu rbx rby rbz vbx vby vbz dvx dvy dvz dt r1x r1y r1z v1x v1y v1z r2x r2y
    r2z v2x v2y v2z dx dy dz) :=
  let (p1x, p1y, p1z, u1x, u1y, u1z) :=
    propagate mu rbx rby rbz (vbx + dvx) (vby + dvy) (vbz + dvz) dt
  let (p0x, p0y, p0z, u0x, u0y, u0z) := propagate mu rbx rby rbz vbx vby vbz dt
  (r1x - r2x + (p1x - p0x) + dx, r1y - r2y + (p1y - p0y) + dy, r1z - r2z + (p1z - p0z) + dz,
    v1x - v2x + (u1x - u0x), v1y - v2y + (u1y - u0y), v1z - v2z + (u1z - u0z))

/-- The encounter after the burn `dv` with the displacement `d`: the miss vector, the projected
covariance, `α` and `e²` of the state after the burn and of the nominal state, `|r1 × ν|²`, and
`|ν|²`. -/
enclosure_def after (mu rbx rby rbz vbx vby vbz dvx dvy dvz dt r1x r1y r1z v1x v1y v1z r2x r2y r2z
    v2x v2y v2z cxx cxy cxz cyy cyz czz dx dy dz) :=
  let (px, py, pz, ux, uy, uz) := relative mu rbx rby rbz vbx vby vbz dvx dvy dvz dt r1x r1y r1z
    v1x v1y v1z r2x r2y r2z v2x v2y v2z dx dy dz
  let (a1, e1) := shape mu rbx rby rbz (vbx + dvx) (vby + dvy) (vbz + dvz)
  let (a0, e0) := shape mu rbx rby rbz vbx vby vbz
  let (m1, m2, c11, c12, c22, xn2, zn2) :=
    plane px py pz ux uy uz r1x r1y r1z cxx cxy cxz cyy cyz czz
  (m1, m2, c11, c12, c22, a1, e1, a0, e0, xn2, zn2)

end Demos.Avoidance
