import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The model of `requirements.md` over the real numbers: the Greenwich mean sidereal time of 1982 in
the form of the function `gstime` of the SGP4 code of AIAA 2006-6753, and the rotation of a TEME
position into the Earth-fixed frame.
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

end Demos.Frames.Model
