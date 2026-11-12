import Demos.Frames.Enclose
import Demos.Geolocation.Model

/-!
The Earth-fixed state of a receiver given in the TEME frame, over the real numbers.  `theta` is
the sidereal angle of the frames demo, `spin` its rate in radians per second of UT1, and
`earthVelocity` the velocity relative to the rotating Earth.  `Derivatives.lean` proves that
`spin` and `earthVelocity` are derivatives (M3 and M2).
-/

open Real

namespace Demos.Geolocation.Model

/-- The rate of the sidereal angle `θ(JD(d, s))` in radians per second of UT1. -/
noncomputable def spin (d s : ℝ) : ℝ :=
  let t := (d - 51544.5 + s / 86400) / 36525
  π / 43200 * (1 + (8640184.812866 + t * (2 * 0.093104 - 3 * 6.2e-6 * t)) / 3155760000)

/-- The sidereal angle of the frames demo at the day `d` and the seconds `s` of UT1. -/
noncomputable def theta (d s : ℝ) : ℝ := Frames.Model.gmst82 (Frames.Model.julian d s)

/-- The velocity relative to the rotating Earth of the TEME position `r` with velocity `v`, at
the sidereal angle `θ` turning at the rate `ω`, with the polar motion `xp` and `yp`:
`E(θ) (v + ω (r₂, −r₁, 0))`. -/
noncomputable def earthVelocity (θ ω xp yp : ℝ) (r v : V3) : V3 :=
  Frames.Model.earthFixed θ xp yp (v.1 + ω * r.2.1, v.2.1 - ω * r.1, v.2.2)

end Demos.Geolocation.Model
