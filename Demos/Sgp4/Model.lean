import Demos.Sgp4.Spec

/-!
The near-Earth SGP4 model of an element set: the status, the position, and the velocity at a time,
as real numbers.  `Spec.lean` defines each quantity, and this file selects the WGS-72 constants
and states the status of `requirements.md`.
-/

namespace Demos.Sgp4.Model

/-- An element set: the mean motion in revolutions per day, the eccentricity, the inclination,
the right ascension of the ascending node, the argument of perigee, and the mean anomaly in
degrees, and the drag term. -/
structure Elements where
  n : ℝ
  e : ℝ
  incl : ℝ
  node : ℝ
  argp : ℝ
  m : ℝ
  bstar : ℝ

/-- The element sets that the model accepts. -/
def Valid (el : Elements) : Prop := 0 < el.n ∧ 0 ≤ el.e ∧ el.e < 1

/-- The period and the constants of an element set, the tuple of `Spec.elements`. -/
noncomputable def constants (el : Elements) :=
  Spec.wgs72 el.n el.e el.incl el.node el.argp el.m el.bstar

/-- The period in minutes. -/
noncomputable def period (el : Elements) : ℝ := (constants el).1

/-- The mean motion `no` in radians per minute. -/
noncomputable def meanMotion (el : Elements) : ℝ := (constants el).2.1

/-- The result of `Spec.state` at `t` minutes from the epoch. -/
noncomputable def outcome (el : Elements) (t : ℝ) := Spec.wgs72State t (constants el)

/-- The mean eccentricity before its lower limit. -/
noncomputable def eccentricity (el : Elements) (t : ℝ) : ℝ := (outcome el t).1

/-- The semilatus rectum in Earth radii. -/
noncomputable def semilatus (el : Elements) (t : ℝ) : ℝ := (outcome el t).2.1

/-- The radius in Earth radii. -/
noncomputable def radius (el : Elements) (t : ℝ) : ℝ := (outcome el t).2.2.1

/-- The position in km in the TEME frame. -/
noncomputable def position (el : Elements) (t : ℝ) : ℝ × ℝ × ℝ :=
  ((outcome el t).2.2.2.1, (outcome el t).2.2.2.2.1, (outcome el t).2.2.2.2.2.1)

/-- The velocity in km/s in the TEME frame. -/
noncomputable def velocity (el : Elements) (t : ℝ) : ℝ × ℝ × ℝ :=
  ((outcome el t).2.2.2.2.2.2.1, (outcome el t).2.2.2.2.2.2.2.1, (outcome el t).2.2.2.2.2.2.2.2)

open Classical in
/-- The status of the model at `t`: 9 for an element set outside `Valid`, 8 for the deep-space
path, 2, 1, 4, and 6 for the errors of the reference code in the order of its tests, and 0
otherwise. -/
noncomputable def status (el : Elements) (t : ℝ) : UInt64 :=
  if ¬Valid el then 9
  else if 225 ≤ period el then 8
  else if meanMotion el ≤ 0 then 2
  else if 1 ≤ eccentricity el t ∨ eccentricity el t < -0.001 then 1
  else if semilatus el t < 0 then 4
  else if radius el t < 1 then 6
  else 0

end Demos.Sgp4.Model
