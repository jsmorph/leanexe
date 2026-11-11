import Demos.Sgp4.Spec

/-!
The two-body limit of the model, theorem S2 of the design.  With `J2`, `J3/J2`, `J4`, and the drag
term set to zero and an eccentricity of at least `10⁻⁶`, the lower limit of the model's mean
eccentricity, `two_body` states that the model's position and velocity are those of the Kepler
orbit with the elements of the element set: the semimajor axis `(xke / n)^(2/3)`, the mean anomaly
`M + n t`, and the eccentric anomaly `E` with `E - e sin E = M + n t`.
-/

open Real

namespace Demos.Sgp4

theorem root_shift {e ω M : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) :
    Kepler.root (e * cos ω) (e * sin ω) (M + ω) = Kepler.root e 0 M + ω := by
  have hsc := sin_sq_add_cos_sq ω
  have h1 : (e * cos ω) ^ 2 + (e * sin ω) ^ 2 < 1 := by
    have : (e * cos ω) ^ 2 + (e * sin ω) ^ 2 = e ^ 2 := by linear_combination e ^ 2 * hsc
    rw [this]; nlinarith
  have h2 : e ^ 2 + (0 : ℝ) ^ 2 < 1 := by nlinarith
  apply (Kepler.lhs_strictMono h1).injective
  rw [Kepler.root_spec h1]
  have hE := Kepler.root_spec h2 M
  unfold Kepler.lhs at hE ⊢
  rw [cos_add, sin_add]
  linear_combination (-1 : ℝ) * hE + e * sin (Kepler.root e 0 M) * hsc

/-- The values of `Spec.anomaly` for the elements of a Kepler orbit. -/
theorem anomaly_two_body {am e ω E : ℝ} (ham : am ≠ 0) (he0 : 0 ≤ e) (he1 : e < 1) :
    Spec.anomaly am (e * cos ω) (e * sin ω) (E + ω) =
      (e * sin E, am * (1 - e ^ 2), am * (1 - e * cos E), √(1 - e ^ 2),
        ((cos E - e) * sin ω + √(1 - e ^ 2) * sin E * cos ω) / (1 - e * cos E),
        ((cos E - e) * cos ω - √(1 - e ^ 2) * sin E * sin ω) / (1 - e * cos E)) := by
  have hω := sin_sq_add_cos_sq ω
  have hβ : √(1 - e ^ 2) ^ 2 = 1 - e ^ 2 := sq_sqrt (by nlinarith)
  have hβ0 : 0 ≤ √(1 - e ^ 2) := sqrt_nonneg _
  have hD : 1 - e * cos E ≠ 0 := by
    have := cos_le_one E
    have : e * cos E < 1 := by nlinarith [neg_one_le_cos E]
    linarith
  have h1 : (1 : ℝ) + √(1 - e ^ 2) ≠ 0 := by linarith
  have e1 : e * cos ω * cos (E + ω) + e * sin ω * sin (E + ω) = e * cos E := by
    rw [cos_add, sin_add]; linear_combination e * cos E * hω
  have e2 : e * cos ω * sin (E + ω) - e * sin ω * cos (E + ω) = e * sin E := by
    rw [cos_add, sin_add]; linear_combination e * sin E * hω
  have e3 : e * cos ω * (e * cos ω) + e * sin ω * (e * sin ω) = e ^ 2 := by
    linear_combination e ^ 2 * hω
  simp only [Spec.anomaly, e1, e2, e3]
  have hq : am / (am * (1 - e * cos E)) = 1 / (1 - e * cos E) := by field_simp
  rw [hq]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))))
  · show 1 / (1 - e * cos E) * (sin (E + ω) - e * sin ω -
      e * cos ω * (e * sin E / (1 + √(1 - e ^ 2)))) = _
    rw [sin_add]
    field_simp
    linear_combination (-(sin E * cos ω)) * hβ
  · show 1 / (1 - e * cos E) * (cos (E + ω) - e * cos ω +
      e * sin ω * (e * sin E / (1 + √(1 - e ^ 2)))) = _
    rw [cos_add]
    field_simp
    linear_combination (sin E * sin ω) * hβ

/-- The position in km and the velocity in km/s on the Kepler orbit with the semimajor axis `a`
in Earth radii, the eccentricity `e`, the inclination `i`, the right ascension of the node `Ω`,
the argument of perigee `ω`, and the eccentric anomaly `E`: the coordinates `a (cos E - e)` and
`a √(1 - e²) sin E` in the orbit's plane and their rates, along the unit vectors `P` toward the
perigee and `Q` a quarter turn ahead of it. -/
noncomputable def twoBody (radius xke a e i Ω ω E : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  let β := √(1 - e ^ 2)
  let r := a * (1 - e * cos E)
  let p := a * (cos E - e)
  let q := a * β * sin E
  let vp := -(√a * sin E) / r
  let vq := √a * β * cos E / r
  let px := cos ω * cos Ω - sin ω * sin Ω * cos i
  let py := cos ω * sin Ω + sin ω * cos Ω * cos i
  let pz := sin ω * sin i
  let qx := -sin ω * cos Ω - cos ω * sin Ω * cos i
  let qy := -sin ω * sin Ω + cos ω * cos Ω * cos i
  let qz := cos ω * sin i
  (radius * (p * px + q * qx), radius * (p * py + q * qy), radius * (p * pz + q * qz),
    (vp * px + vq * qx) * (radius * xke / 60), (vp * py + vq * qy) * (radius * xke / 60),
    (vp * pz + vq * qz) * (radius * xke / 60))

/-- The identity behind the velocity: the radial and the transverse rates along the directions
of the true anomaly are the rates along `P` and `Q`. -/
theorem rates {e sE cE β P Q : ℝ} (hE : sE ^ 2 + cE ^ 2 = 1) (hβ : β ^ 2 = 1 - e ^ 2) :
    e * sE * ((cE - e) * P + β * sE * Q) + β * ((cE - e) * Q - β * sE * P) =
      (-sE * P + β * cE * Q) * (1 - e * cE) := by
  linear_combination (-(P * sE)) * hβ + Q * β * e * hE

/-- **S2.**  Without the perturbations, the model is the Kepler orbit of its elements. -/
theorem two_body (radius mu n e incl node argp m t : ℝ) (hr : 0 < radius) (hmu : 0 < mu)
    (hn : 0 < n) (he : (1.0e-6 : ℝ) ≤ e) (he1 : e < 1) :
    Spec.stateAt radius 0 t (Spec.elements radius mu 0 0 0 n e incl node argp m 0) =
      (e, (Spec.xkeOf radius mu / (n / (1440 / (2 * π)))) ^ (2 / 3 : ℝ) * (1 - e ^ 2),
        (Spec.xkeOf radius mu / (n / (1440 / (2 * π)))) ^ (2 / 3 : ℝ) *
          (1 - e * cos (Kepler.root e 0 (m * (π / 180) + n / (1440 / (2 * π)) * t))),
        twoBody radius (Spec.xkeOf radius mu)
          ((Spec.xkeOf radius mu / (n / (1440 / (2 * π)))) ^ (2 / 3 : ℝ)) e (incl * (π / 180))
          (node * (π / 180)) (argp * (π / 180))
          (Kepler.root e 0 (m * (π / 180) + n / (1440 / (2 * π)) * t))) := by
  have he0 : 0 ≤ e := by linarith
  have hx : 0 < 60 / √(radius * radius * radius / mu) := by positivity
  have hn0 : 0 < n / (1440 / (2 * π)) := by positivity
  have ha : 0 < (60 / √(radius * radius * radius / mu) / (n / (1440 / (2 * π)))) ^ (2 / 3 : ℝ) :=
    rpow_pos_of_pos (div_pos hx hn0) _
  simp only [Spec.stateAt, Spec.elements, Spec.state, Spec.constants, Spec.convert, Spec.xkeOf,
    Spec.period, Spec.unkozai, Spec.geometry, Spec.atmosphere, Spec.dragCoef, Spec.dragInner,
    Spec.dragC4, Spec.dragC5, Spec.ratesMean, Spec.ratesAngles, Spec.coupling, Spec.epochTerms,
    Spec.higherD, Spec.higherT, Spec.secular, Spec.drag, Spec.mean, Spec.longPeriod,
    Spec.shortRadius, Spec.shortAngles, Spec.orientation, Spec.vectors, mul_zero,
    zero_mul, zero_div, add_zero, sub_zero, neg_zero, ite_self, div_one, mul_one, cos_zero,
    sin_zero, max_eq_left he, twoBody]
  rw [root_shift he0 he1, anomaly_two_body ha.ne' he0 he1]
  generalize (60 / √(radius * radius * radius / mu) / (n / (1440 / (2 * π)))) ^ (2 / 3 : ℝ) = a
    at ha ⊢
  generalize Kepler.root e 0 (m * (π / 180) + n / (1440 / (2 * π)) * t) = E
  generalize argp * (π / 180) = ω
  generalize node * (π / 180) = Ω
  generalize incl * (π / 180) = i
  generalize 60 / √(radius * radius * radius / mu) = xke
  have hE := sin_sq_add_cos_sq E
  have hβ : √(1 - e ^ 2) ^ 2 = 1 - e ^ 2 := sq_sqrt (by nlinarith)
  have hD : 1 - e * cos E ≠ 0 := by
    have : e * cos E < 1 := by nlinarith [neg_one_le_cos E, cos_le_one E]
    linarith
  have ha' := ha.ne'
  have hs : √(a * (1 - e ^ 2)) = √a * √(1 - e ^ 2) := sqrt_mul ha.le _
  simp only [hs]
  generalize √(1 - e ^ 2) = β at hβ ⊢
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_
    (Prod.ext ?_ (Prod.ext ?_ ?_)))))))
  · show _ = _
    field_simp
    ring
  · show _ = _
    field_simp
    ring
  · show _ = _
    field_simp
  · have k := rates (P := cos ω * cos Ω - sin ω * sin Ω * cos i)
      (Q := -sin ω * cos Ω - cos ω * sin Ω * cos i) hE hβ
    show _ = _
    field_simp
    linear_combination xke * k
  · have k := rates (P := cos ω * sin Ω + sin ω * cos Ω * cos i)
      (Q := -sin ω * sin Ω + cos ω * cos Ω * cos i) hE hβ
    show _ = _
    field_simp
    linear_combination xke * k
  · have k := rates (P := sin ω * sin i) (Q := cos ω * sin i) hE hβ
    show _ = _
    field_simp
    linear_combination xke * k

end Demos.Sgp4
