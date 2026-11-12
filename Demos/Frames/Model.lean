import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The model of `requirements.md` over the real numbers: the Greenwich mean sidereal time of 1982 in
the form of the function `gstime` of the SGP4 code of AIAA 2006-6753, the rotation of a TEME
position into the Earth-fixed frame, the position of geodetic coordinates on the WGS 84 ellipsoid,
and TAI − UTC from a leap-second table.
-/

open Real

namespace Demos.Frames.Model

/-! ### Sidereal time -/

/-- The Julian date of the Modified Julian Date `d` and `s` seconds. -/
noncomputable def julian (d s : ℝ) : ℝ := 2400000.5 + d + s / 86400

/-- The Greenwich mean sidereal time of 1982 in radians at the Julian date `jd` of UT1, before
the reduction to `[0, 2π)`. -/
noncomputable def gmst82 (jd : ℝ) : ℝ :=
  let t := (jd - 2451545) / 36525
  2 * π / 86400 * (67310.54841 + (876600 * 3600 + 8640184.812866) * t + 0.093104 * t ^ 2 -
    6.2e-6 * t ^ 3)

/-! ### The Earth-fixed frame -/

/-- The rotation of the frame by `α` about the first axis, as SOFA's `iauRx`. -/
noncomputable def rx (α : ℝ) (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (v.1, cos α * v.2.1 + sin α * v.2.2, -sin α * v.2.1 + cos α * v.2.2)

/-- The rotation of the frame by `α` about the second axis, as SOFA's `iauRy`. -/
noncomputable def ry (α : ℝ) (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (cos α * v.1 - sin α * v.2.2, v.2.1, sin α * v.1 + cos α * v.2.2)

/-- The rotation of the frame by `α` about the third axis, as SOFA's `iauRz`. -/
noncomputable def rz (α : ℝ) (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (cos α * v.1 + sin α * v.2.1, -sin α * v.1 + cos α * v.2.1, v.2.2)

/-- Radians per arcsecond. -/
noncomputable def arcsec : ℝ := π / 648000

/-- The Earth-fixed position of the TEME position `r` at the sidereal angle `θ`, with the polar
motion `xp` and `yp` in arcseconds. -/
noncomputable def earthFixed (θ xp yp : ℝ) (r : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  rx (-(yp * arcsec)) (ry (-(xp * arcsec)) (rz θ r))

/-! ### Geodetic coordinates -/

/-- The semimajor axis of WGS 84 in km. -/
noncomputable def a : ℝ := 6378.137

/-- The flattening of WGS 84. -/
noncomputable def f : ℝ := 1 / 298.257223563

/-- The square of the eccentricity. -/
noncomputable def e2 : ℝ := f * (2 - f)

/-- The radius of curvature in the prime vertical at the latitude `φ`. -/
noncomputable def radius (φ : ℝ) : ℝ := a / √(1 - e2 * sin φ ^ 2)

/-- The Earth-fixed position of the latitude `φ`, the longitude `lon`, and the height `h`. -/
noncomputable def position (φ lon h : ℝ) : ℝ × ℝ × ℝ :=
  ((radius φ + h) * cos φ * cos lon, (radius φ + h) * cos φ * sin lon,
    (radius φ * (1 - e2) + h) * sin φ)

/-- `(φ, lon, h)` are geodetic coordinates of `(x, y, z)`: the latitude lies in `(−π/2, π/2)`,
`N(φ) + h > 0`, which puts the point and its foot point on the ellipsoid in the same half meridian
plane, and the position is the point. -/
def IsGeodetic (x y z φ lon h : ℝ) : Prop :=
  |φ| < π / 2 ∧ 0 < radius φ + h ∧ position φ lon h = (x, y, z)

/-- The domain `D` of `requirements.md`: off the polar axis, and outside the cylinder about the
center. -/
def InDomain (x y z : ℝ) : Prop :=
  0 < √(x ^ 2 + y ^ 2) ∧ (a * e2 < √(x ^ 2 + y ^ 2) ∨ a * e2 / (1 - f) < |z|)

/-! ### Time scales -/

/-- The number of entries of a table `E, d₀, Δ₀, d₁, Δ₁, …`. -/
def count (xs : Array UInt64) : ℕ := (xs.size - 1) / 2

/-- The date of entry `i`. -/
def date (xs : Array UInt64) (i : ℕ) : UInt64 := xs[2 * i + 1]!

/-- The offset TAI − UTC of entry `i`. -/
def offset (xs : Array UInt64) (i : ℕ) : UInt64 := xs[2 * i + 2]!

/-- `Δ` is TAI − UTC on the day `d` by the table `xs`: the offset of the last entry whose date is
at most `d`. -/
def LeapOffset (xs : Array UInt64) (d Δ : UInt64) : Prop :=
  ∃ i < count xs, date xs i ≤ d ∧ offset xs i = Δ ∧ ∀ j < count xs, i < j → d < date xs j

/-- A valid table: an odd size of at least 3, every value below `2³²`, strictly increasing dates,
and an expiry `E = xs[0]` above the last date. -/
def ValidTable (xs : Array UInt64) : Prop :=
  3 ≤ xs.size ∧ xs.size % 2 = 1 ∧ (∀ i < xs.size, xs[i]!.toNat < 2 ^ 32) ∧
    (∀ i j, i < j → j < count xs → date xs i < date xs j) ∧ date xs (count xs - 1) < xs[0]!

end Demos.Frames.Model
