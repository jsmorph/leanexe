import Library.Numerics.Interval.Enclose
import Library.Numerics.Float64.Atan.AtanTheorem
import Demos.Frames.Geodetic

/-!
The formulas of `requirements.md` in interval arithmetic.  Each `enclosure_def` declares a real
function, its interval function, whose name ends in `I`, and the theorem `encloses` that the
interval function's result contains the real function's result when each interval argument
contains the real argument.  The theorems at the end equate the real functions with the model.
-/

open Real

namespace Demos.Frames

/-- The seconds `W(d, s)` of the sidereal time of the day `d` and the seconds `s` of UT1. -/
enclosure_def gmstSeconds (d s) :=
  let t := (d - 51544.5 + s / 86400) / 36525
  s + 24110.54841 + t * (8640184.812866 + t * (0.093104 - 6.2e-6 * t))

/-- The angle of `w - 86400 n` seconds of sidereal time. -/
enclosure_def turns (w n) := (w - 86400 * n) * (π / 43200)

/-- The rotation `R1(−yp) R2(−xp) R3(ψ)` of the position `(x, y, z)`, with `xp` and `yp` in
arcseconds. -/
enclosure_def toEarth (ψ xp yp x y z) :=
  let c := cos ψ
  let s := sin ψ
  let u := c * x + s * y
  let v := c * y - s * x
  let ax := xp * (π / 648000)
  let ay := yp * (π / 648000)
  let cx := cos ax
  let sx := sin ax
  let cy := cos ay
  let sy := sin ay
  let w := cx * z - sx * u
  (cx * u + sx * z, cy * v - sy * w, sy * v + cy * w)

set_option linter.unusedVariables false in
/-- The arctangents of the points of an interval: the library's `atan` at the endpoints, each
moved two steps outward.  The tables are those of the interval functions, which it does not use. -/
def arctanI (inv half logTab expTab : Array UInt64) (a : Library.Numerics.Interval.Interval) :
    Library.Numerics.Interval.Interval :=
  Library.Numerics.Interval.increasing a (Library.Numerics.Float64.Atan.atan a.lo)
    (Library.Numerics.Float64.Atan.atan a.hi)

open Library.Numerics.Interval in
@[enclose] theorem arctan.encloses {powLog powExp : Array UInt64} {a : Interval} {x : ℝ}
    (ha : Encloses a x) :
    Encloses (arctanI Library.Numerics.Float64.Trig.invPi Library.Numerics.Float64.Trig.halfPi
      powLog powExp a) (arctan x) := by
  intro h
  unfold arctanI at h ⊢
  obtain ⟨sa, hc⟩ := increasing_sound h (arctan_strictMono.monotone.monotoneOn _)
    (fun f => Library.Numerics.Float64.Atan.AtanTheorem.atan_within_one _ f)
    (fun f => Library.Numerics.Float64.Atan.AtanTheorem.atan_within_one _ f)
  exact hc x (ha sa)


/-- The Earth-fixed position of the latitude, the longitude, and the height on WGS 84. -/
enclosure_def cartesian (lat lon h) :=
  let f := 1 / 298.257223563
  let e2 := f * (2 - f)
  let s := sin lat
  let n := 6378.137 / √(1 - e2 * (s * s))
  let c := cos lat
  ((n + h) * c * cos lon, (n + h) * c * sin lon, (n * (1 - e2) + h) * s)

/-- The slope bound `p − a e²` of `k`. -/
enclosure_def slopeA (p) :=
  let f := 1 / 298.257223563
  p - 6378.137 * (f * (2 - f))

/-- The residual `k(u)`. -/
enclosure_def residualA (p z u) :=
  let f := 1 / 298.257223563
  let e2 := f * (2 - f)
  p * u - z - 6378.137 * e2 * u / √(1 + (1 - e2) * (u * u))

/-- The latitude and the height from the root `u` of `k`. -/
enclosure_def coordsA (p z u) :=
  let f := 1 / 298.257223563
  let e2 := f * (2 - f)
  (arctan u, (p + z * u - 6378.137 * √(1 + (1 - e2) * (u * u))) / √(1 + u * u))

/-- The excess `z − a e²/(1 − f)` of `z` over the half-height of the cylinder about the center. -/
enclosure_def slopeB (z) :=
  let f := 1 / 298.257223563
  z - 6378.137 * (f * (2 - f)) / (1 - f)

/-- The residual `ℓ(v)`. -/
enclosure_def residualB (p z v) :=
  let f := 1 / 298.257223563
  let e2 := f * (2 - f)
  z * v + 6378.137 * e2 * v / √(v * v + (1 - e2)) - p

/-- The latitude and the height from the root `v` of `ℓ`. -/
enclosure_def coordsB (p z v) :=
  let f := 1 / 298.257223563
  let e2 := f * (2 - f)
  (π / 2 - arctan v, (p * v + z - 6378.137 * √(v * v + (1 - e2))) / √(1 + v * v))

/-- The longitude `2 arctan(y/q)` for `q = p + x`. -/
enclosure_def lonA (y q) := 2 * arctan (y / q)

/-- The longitude `π − 2 arctan(y/q)` for `q = p − x`. -/
enclosure_def lonB (y q) := π - 2 * arctan (y / q)

/-- The sidereal angle is `2π (d − 51544)` plus the angle of `W(d, s)` seconds. -/
theorem gmst82_eq (d s : ℝ) :
    Model.gmst82 (Model.julian d s) = 2 * π * (d - 51544) + gmstSeconds d s * (π / 43200) := by
  simp only [Model.gmst82, Model.julian, gmstSeconds]
  ring

/-- The angle of `turns` is the sidereal angle less a whole number of turns. -/
theorem turns_eq (d s : ℝ) (n : ℤ) :
    turns (gmstSeconds d s) n = Model.gmst82 (Model.julian d s) - 2 * π * ((d - 51544) + n) := by
  rw [gmst82_eq]
  simp only [turns]
  ring

/-- `toEarth` is the rotation of the model. -/
theorem toEarth_eq (ψ xp yp x y z : ℝ) :
    toEarth ψ xp yp x y z = Model.earthFixed ψ xp yp (x, y, z) := by
  simp only [toEarth, Model.earthFixed, Model.rx, Model.ry, Model.rz, Model.arcsec, cos_neg,
    sin_neg, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- The rotation depends on the angle only modulo `2π`. -/
theorem toEarth_periodic (ψ xp yp x y z : ℝ) (k : ℤ) :
    toEarth (ψ - 2 * π * k) xp yp x y z = toEarth ψ xp yp x y z := by
  have hc : cos (ψ - 2 * π * k) = cos ψ := by
    rw [show ψ - 2 * π * k = ψ - k * (2 * π) by ring]; exact cos_sub_int_mul_two_pi ψ k
  have hs : sin (ψ - 2 * π * k) = sin ψ := by
    rw [show ψ - 2 * π * k = ψ - k * (2 * π) by ring]; exact sin_sub_int_mul_two_pi ψ k
  simp only [toEarth, hc, hs]

theorem sq_abs_sum (x y : ℝ) : |x| * |x| + |y| * |y| = x ^ 2 + y ^ 2 := by
  rw [abs_mul_abs_self, abs_mul_abs_self]; ring

/-- The distance `p` of `(x, y, z)` from the polar axis: the square root of `x² + y²`, whose
interval the program clamps at zero, since outward rounding moves an exact zero one step below
it. -/
def axisI (x y : Library.Numerics.Interval.Interval) : Library.Numerics.Interval.Interval :=
  let q := Library.Numerics.Interval.add
    (Library.Numerics.Interval.mul (Library.Numerics.Interval.abs x) (Library.Numerics.Interval.abs x))
    (Library.Numerics.Interval.mul (Library.Numerics.Interval.abs y) (Library.Numerics.Interval.abs y))
  Library.Numerics.Interval.sqrt (Library.Numerics.Interval.clamp q 0 q.hi)

open Library.Numerics.Interval in
theorem axis_encloses {x y : Interval} {x' y' : ℝ} (hx : Encloses x x') (hy : Encloses y y') :
    Encloses (axisI x y) (√(x' ^ 2 + y' ^ 2)) := by
  have hq := encloses_add (encloses_mul (encloses_abs hx) (encloses_abs hx))
    (encloses_mul (encloses_abs hy) (encloses_abs hy))
  have hnn : 0 ≤ |x'| * |x'| + |y'| * |y'| := by positivity
  unfold axisI
  generalize add (mul (abs x) (abs x)) (mul (abs y) (abs y)) = q at hq ⊢
  have hc : Encloses (clamp q 0 q.hi) (|x'| * |x'| + |y'| * |y'|) := fun h => by
    obtain ⟨s, hc⟩ := clamp_sound h
    have c := hq s
    exact hc _ c (by rw [zero_value.2]; exact hnn) c.2.2.2.2
  have := encloses_sqrt hc
  rwa [sq_abs_sum] at this

theorem cartesian_eq (lat lon h : ℝ) : cartesian lat lon h = Model.position lat lon h := by
  simp only [cartesian, Model.position, Model.radius, Model.a, Model.e2, Model.f, pow_two]

theorem slopeA_eq (p : ℝ) : slopeA p = p - Model.a * Model.e2 := by
  simp only [slopeA, Model.a, Model.e2, Model.f]

theorem residualA_eq (p z u : ℝ) :
    residualA p z u = Geodetic.kA (Model.a * Model.e2) (1 - Model.e2) p z u := by
  simp only [residualA, Geodetic.kA, Model.a, Model.e2, Model.f, pow_two]

theorem coordsA_eq (p z u : ℝ) : coordsA p z u =
    (arctan u, (p + z * u - Model.a * √(1 + (1 - Model.e2) * u ^ 2)) / √(1 + u ^ 2)) := by
  simp only [coordsA, Model.a, Model.e2, Model.f, pow_two]

theorem slopeB_eq (z : ℝ) : slopeB z = z - Model.a * Model.e2 / (1 - Model.f) := by
  simp only [slopeB, Model.a, Model.e2, Model.f]

theorem residualB_eq (p z v : ℝ) :
    residualB p z v = Geodetic.lB (Model.a * Model.e2) (1 - Model.e2) p z v := by
  simp only [residualB, Geodetic.lB, Model.a, Model.e2, Model.f, pow_two]

theorem coordsB_eq (p z v : ℝ) : coordsB p z v =
    (π / 2 - arctan v, (p * v + z - Model.a * √(v ^ 2 + (1 - Model.e2))) / √(1 + v ^ 2)) := by
  simp only [coordsB, Model.a, Model.e2, Model.f, pow_two]

end Demos.Frames
