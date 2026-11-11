import Demos.Orbit.Newton
import Demos.Sgp4.Kepler

/-!
The motion along an elliptic orbit by Kepler's equation.  For a state `(r, v)` with
`2/|r| - |v|²/μ > 0`, the orbit is an ellipse with the semimajor axis `a` of the vis-viva
equation `|v|² = μ (2/|r| - 1/a)` and the mean motion `n = √(μ/a³)`, and `ε cos E₀ = 1 - |r|/a`
and `ε sin E₀ = (r · v)/√(μ a)` give its eccentricity `ε` and the eccentric anomaly `E₀` of `r`.
When the eccentric anomaly advances from `E₀` to `E₀ + φ`, the position is `f r + g v` with
Lagrange's coefficients `f = 1 - (a/|r|) (1 - cos φ)` and
`g = ((|r|/a) sin φ + ε sin E₀ (1 - cos φ))/n` (`keplerPos`), and Kepler's equation gives the
time `(M(E₀ + φ) - M(E₀))/n` with the mean anomaly `M(E) = E - ε sin E` (`keplerTime`).

`keplerPos_onPath` states that each such position lies on the path of the state's orbit, and
`kepler_radius` that its length is `a (1 - ε cos(E₀ + φ))`.  `keplerTime_strictMono` states that
the time increases with `φ`, and `keplerPos_inj` that the positions for two values of `φ` less
than `2π` apart are distinct, so that `EllipticTransfer` names the first arrival at a position.

`keplerAdvance` inverts Kepler's equation, and `kepler_newton` states that the position
`keplerPos` and the velocity `keplerVel` at the advance `keplerAdvance τ` solve Newton's
equation `r'' = -μ r/|r|³` and are at `(r, v)` at the time 0: the motion that Kepler's equation
describes is a two-body motion of `Newton.lean` through the state `(r, v)`.
-/

namespace Demos.Orbit

open V3 Real

/-- The semimajor axis of the state's orbit, from the vis-viva equation
`|v|² = μ (2/|r| - 1/a)`. -/
noncomputable def semimajor (μ : ℝ) (r v : V3) : ℝ := (2 / norm r - dot v v / μ)⁻¹

/-- The mean motion `n = √(μ/a³)`. -/
noncomputable def meanMotion (μ : ℝ) (r v : V3) : ℝ := √(μ / semimajor μ r v ^ 3)

/-- `ε cos E₀ = 1 - |r|/a` for the eccentricity `ε` and the eccentric anomaly `E₀` of the
state. -/
noncomputable def eCos (μ : ℝ) (r v : V3) : ℝ := 1 - norm r / semimajor μ r v

/-- `ε sin E₀ = (r · v)/√(μ a)`. -/
noncomputable def eSin (μ : ℝ) (r v : V3) : ℝ := dot r v / √(μ * semimajor μ r v)

/-- The time in which the eccentric anomaly advances from `E₀` to `E₀ + φ`, by Kepler's
equation: `(M(E₀ + φ) - M(E₀))/n` with `M(E) = E - ε sin E`.  With `a = ε cos E₀` and
`b = -ε sin E₀`, `M(E₀ + φ) - M(E₀) = φ + b cos φ - a sin φ - b`, the left side of Kepler's
equation in the form of the SGP4 demo less `b`. -/
noncomputable def keplerTime (μ : ℝ) (r v : V3) (φ : ℝ) : ℝ :=
  (Sgp4.Kepler.lhs (eCos μ r v) (-eSin μ r v) φ + eSin μ r v) / meanMotion μ r v

/-- The position after the eccentric anomaly advances by `φ`: `f r + g v` with Lagrange's
coefficients `f = 1 - (a/|r|) (1 - cos φ)` and `g = ((|r|/a) sin φ + ε sin E₀ (1 - cos φ))/n`. -/
noncomputable def keplerPos (μ : ℝ) (r v : V3) (φ : ℝ) : V3 :=
  (1 - semimajor μ r v / norm r * (1 - cos φ)) • r +
    ((norm r / semimajor μ r v * sin φ + eSin μ r v * (1 - cos φ)) / meanMotion μ r v) • v

/-- The motion from the state `(r, v)` along its elliptic orbit first reaches `r'` after the
time `t`: the orbit is an ellipse, `r × v ≠ 0`, and the eccentric anomaly advances by some `φ`
with `0 < φ < 2π` to the position `r'` in the time `t` of Kepler's equation.  `keplerPos_inj`
makes `φ` the only advance in `[0, 2π)` that reaches `r'`, and `keplerTime_strictMono` makes `t`
the least positive time at which the motion is at `r'`. -/
def EllipticTransfer (μ : ℝ) (r v r' : V3) (t : ℝ) : Prop :=
  0 < 2 / norm r - dot v v / μ ∧ 0 < dot (cross r v) (cross r v) ∧
    ∃ φ, 0 < φ ∧ φ < 2 * π ∧ keplerPos μ r v φ = r' ∧ keplerTime μ r v φ = t

/-! ### The orbit's constants -/

theorem dot_basis (a b : ℝ) (r1 r2 : V3) :
    dot (a • r1 + b • r2) (a • r1 + b • r2) =
      a ^ 2 * dot r1 r1 + 2 * a * b * dot r1 r2 + b ^ 2 * dot r2 r2 := by
  simp only [dot, add_x, add_y, add_z, smul_x, smul_y, smul_z]; ring

theorem dot_basis_left (a b : ℝ) (r1 r2 : V3) :
    dot r1 (a • r1 + b • r2) = a * dot r1 r1 + b * dot r1 r2 := by
  simp only [dot, add_x, add_y, add_z, smul_x, smul_y, smul_z]; ring

theorem cross_basis (a b : ℝ) (r1 r2 : V3) :
    cross r1 (a • r1 + b • r2) = b • cross r1 r2 := by
  ext <;> simp only [cross_x, cross_y, cross_z, add_x, add_y, add_z, smul_x, smul_y, smul_z]
    <;> ring

theorem cross_basis_right (a b : ℝ) (r v : V3) :
    cross v (a • r + b • v) = (-a) • cross r v := by
  ext <;> simp only [cross_x, cross_y, cross_z, add_x, add_y, add_z, smul_x, smul_y, smul_z]
    <;> ring


/-- The relations among the state, `a`, `n`, `ε cos E₀`, and `ε sin E₀` for an elliptic state
with `r × v ≠ 0`. -/
theorem kepler_basics {μ : ℝ} (hμ : 0 < μ) {r v : V3} (hr : 0 < norm r)
    (he : 0 < 2 / norm r - dot v v / μ) (hh : 0 < dot (cross r v) (cross r v)) :
    0 < semimajor μ r v ∧ 0 < meanMotion μ r v ∧
      meanMotion μ r v ^ 2 * semimajor μ r v ^ 3 = μ ∧
      norm r = semimajor μ r v * (1 - eCos μ r v) ∧
      dot r v = eSin μ r v * meanMotion μ r v * semimajor μ r v ^ 2 ∧
      dot v v = μ * (2 / norm r - 1 / semimajor μ r v) ∧
      dot (cross r v) (cross r v) / μ =
        semimajor μ r v * (1 - eCos μ r v ^ 2 - eSin μ r v ^ 2) ∧
      eCos μ r v ^ 2 + eSin μ r v ^ 2 < 1 := by
  have ha : 0 < semimajor μ r v := inv_pos.mpr he
  have hn : 0 < meanMotion μ r v := sqrt_pos.mpr (by positivity)
  have hn2 : meanMotion μ r v ^ 2 * semimajor μ r v ^ 3 = μ := by
    rw [meanMotion, sq_sqrt (by positivity)]; field_simp
  have hroot : √(μ * semimajor μ r v) = meanMotion μ r v * semimajor μ r v ^ 2 := by
    rw [← sqrt_sq (by positivity : 0 ≤ meanMotion μ r v * semimajor μ r v ^ 2)]
    congr 1
    linear_combination (-semimajor μ r v) * hn2
  have hv : dot v v = μ * (2 / norm r - 1 / semimajor μ r v) := by
    rw [semimajor, one_div, inv_inv]; field_simp; ring
  have hl : dot (cross r v) (cross r v) = norm r ^ 2 * dot v v - dot r v ^ 2 := by
    rw [norm_sq]; simp only [dot, cross_x, cross_y, cross_z]; ring
  have hp : dot (cross r v) (cross r v) / μ =
      semimajor μ r v * (1 - eCos μ r v ^ 2 - eSin μ r v ^ 2) := by
    rw [eCos, eSin, hroot, hl, hv]
    generalize semimajor μ r v = a at ha hn2 ⊢
    generalize meanMotion μ r v = n at hn hn2 ⊢
    subst hn2
    field_simp
    ring
  refine ⟨ha, hn, hn2, ?_, ?_, hv, hp, ?_⟩
  · rw [eCos]; field_simp; ring
  · rw [eSin, hroot]; field_simp
  · have : 0 < dot (cross r v) (cross r v) / μ := div_pos hh hμ
    rw [hp] at this
    have := (pos_iff_pos_of_mul_pos this).mp ha
    linarith

theorem keplerPos_zero (μ : ℝ) (r v : V3) : keplerPos μ r v 0 = r := by
  ext <;> simp [keplerPos]

theorem keplerTime_zero (μ : ℝ) (r v : V3) : keplerTime μ r v 0 = 0 := by
  simp [keplerTime, Sgp4.Kepler.lhs]

/-- The time of Kepler's equation increases with the advance of the eccentric anomaly. -/
theorem keplerTime_strictMono {μ : ℝ} (hμ : 0 < μ) {r v : V3} (hr : 0 < norm r)
    (he : 0 < 2 / norm r - dot v v / μ) (hh : 0 < dot (cross r v) (cross r v)) :
    StrictMono (keplerTime μ r v) := by
  obtain ⟨-, hn, -, -, -, -, -, hε⟩ := kepler_basics hμ hr he hh
  have hm := Sgp4.Kepler.lhs_strictMono (a := eCos μ r v) (b := -eSin μ r v)
    (by rw [neg_sq]; exact hε)
  intro φ1 φ2 h
  unfold keplerTime
  exact div_lt_div_of_pos_right (by linarith [hm h]) hn

/-- `|AC - BS| < 1` for `A² + B² < 1` and `C² + S² = 1`. -/
theorem combo_lt_one {A B C S : ℝ} (hAB : A ^ 2 + B ^ 2 < 1) (hCS : S ^ 2 + C ^ 2 = 1) :
    A * C - B * S < 1 := by
  have h : (A * C - B * S) ^ 2 < 1 ^ 2 := by
    nlinarith [sq_nonneg (A * S + B * C)]
  exact (abs_lt_of_sq_lt_sq' h one_pos.le).2

/-- The length of the position: `a (1 - ε cos(E₀ + φ))`. -/
theorem kepler_radius {μ : ℝ} (hμ : 0 < μ) {r v : V3} (hr : 0 < norm r)
    (he : 0 < 2 / norm r - dot v v / μ) (hh : 0 < dot (cross r v) (cross r v)) (φ : ℝ) :
    norm (keplerPos μ r v φ) =
      semimajor μ r v * (1 - eCos μ r v * cos φ + eSin μ r v * sin φ) := by
  obtain ⟨ha, hn, hn2, hr1, hrv, hv, -, hε⟩ := kepler_basics hμ hr he hh
  have hpos : 0 < 1 - eCos μ r v * cos φ + eSin μ r v * sin φ := by
    have := combo_lt_one hε (sin_sq_add_cos_sq φ); linarith
  have hsq := sin_sq_add_cos_sq φ
  rw [V3.norm, keplerPos, dot_basis, ← norm_sq, hrv, hv]
  rw [← sqrt_sq (by positivity : 0 ≤ semimajor μ r v * (1 - eCos μ r v * cos φ +
    eSin μ r v * sin φ))]
  congr 1
  rw [hr1]
  have h1A : 0 < 1 - eCos μ r v := (pos_iff_pos_of_mul_pos (hr1 ▸ hr)).mp ha
  generalize semimajor μ r v = a at *
  generalize meanMotion μ r v = n at *
  generalize eCos μ r v = A at *
  generalize eSin μ r v = B at *
  subst hn2
  field_simp
  rw [← sub_eq_zero]
  ring_nf
  simp only [sin_sq]
  ring

theorem dot_lin (e r v : V3) (f g : ℝ) : dot e (f • r + g • v) = f * dot e r + g * dot e v := by
  simp only [dot, add_x, add_y, add_z, smul_x, smul_y, smul_z]; ring

/-- Each position of the motion lies on the path of the state's orbit. -/
theorem keplerPos_onPath {μ : ℝ} (hμ : 0 < μ) {r v : V3} (hr : 0 < norm r)
    (he : 0 < 2 / norm r - dot v v / μ) (hh : 0 < dot (cross r v) (cross r v)) (φ : ℝ) :
    OnPath μ (orbitOf μ r v) (keplerPos μ r v φ) := by
  obtain ⟨ha, hn, -, hr1, hrv, -, hp, hε⟩ := kepler_basics hμ hr he hh
  have hpos : 0 < 1 - eCos μ r v * cos φ + eSin μ r v * sin φ := by
    have := combo_lt_one hε (sin_sq_add_cos_sq φ); linarith
  have hrad := kepler_radius hμ hr he hh φ
  have h1A : 0 < 1 - eCos μ r v := (pos_iff_pos_of_mul_pos (hr1 ▸ hr)).mp ha
  refine ⟨hh, by rw [hrad]; positivity, ?_, ?_⟩
  · simp only [orbitOf, keplerPos, dot, add_x, add_y, add_z, smul_x, smul_y, smul_z, cross_x,
      cross_y, cross_z]
    ring
  · have edr : dot (μ⁻¹ • cross v (cross r v) - (norm r)⁻¹ • r) r =
        dot (cross r v) (cross r v) / μ - norm r := by
      have h1 : dot (μ⁻¹ • cross v (cross r v) - (norm r)⁻¹ • r) r =
          μ⁻¹ * dot (cross r v) (cross r v) - (norm r)⁻¹ * dot r r := by
        simp only [dot, sub_x, sub_y, sub_z, smul_x, smul_y, smul_z, cross_x, cross_y, cross_z]
        ring
      rw [h1, ← norm_sq r]; field_simp
    have edv : dot (μ⁻¹ • cross v (cross r v) - (norm r)⁻¹ • r) v = -(dot r v / norm r) := by
      have h1 : dot (μ⁻¹ • cross v (cross r v) - (norm r)⁻¹ • r) v =
          -((norm r)⁻¹ * dot r v) := by
        simp only [dot, sub_x, sub_y, sub_z, smul_x, smul_y, smul_z, cross_x, cross_y, cross_z]
        ring
      rw [h1]; field_simp
    rw [hrad]
    simp only [orbitOf, keplerPos]
    rw [dot_lin, edr, edv, hp, hrv]
    rw [hr1]
    generalize semimajor μ r v = a at *
    generalize meanMotion μ r v = n at *
    generalize eCos μ r v = A at *
    generalize eSin μ r v = B at *
    field_simp
    ring

theorem smul_cancel {a b : ℝ} {h : V3} (hh : 0 < dot h h) (e : a • h = b • h) : a = b := by
  have := congrArg (dot h) e
  rw [dot_smul, dot_smul] at this
  exact mul_right_cancel₀ hh.ne' this

/-- Positions for two advances of the eccentric anomaly less than `2π` apart are distinct. -/
theorem keplerPos_inj {μ : ℝ} (hμ : 0 < μ) {r v : V3} (hr : 0 < norm r)
    (he : 0 < 2 / norm r - dot v v / μ) (hh : 0 < dot (cross r v) (cross r v)) {φ1 φ2 : ℝ}
    (hφ : |φ1 - φ2| < 2 * π) (heq : keplerPos μ r v φ1 = keplerPos μ r v φ2) : φ1 = φ2 := by
  obtain ⟨ha, hn, -, hr1, -, -, -, -⟩ := kepler_basics hμ hr he hh
  have hg := smul_cancel hh (by
    have := congrArg (cross r) heq
    simp only [keplerPos, cross_basis] at this
    exact this)
  have hf := smul_cancel hh (by
    have := congrArg (cross v) heq
    simp only [keplerPos, cross_basis_right] at this
    exact this)
  have hc : cos φ1 = cos φ2 := by
    have h := neg_inj.mp hf
    have hq : semimajor μ r v / norm r ≠ 0 := (div_pos ha hr).ne'
    have : semimajor μ r v / norm r * (1 - cos φ1) = semimajor μ r v / norm r * (1 - cos φ2) := by
      linarith
    have := mul_left_cancel₀ hq this
    linarith
  have hs : sin φ1 = sin φ2 := by
    rw [hc] at hg
    have h := (div_left_inj' hn.ne').mp hg
    have hq : norm r / semimajor μ r v ≠ 0 := (div_pos hr ha).ne'
    exact mul_left_cancel₀ hq (by linarith)
  have h1 : cos (φ1 - φ2) = 1 := by
    rw [cos_sub, hc, hs]
    linear_combination sin_sq_add_cos_sq φ2
  obtain ⟨m, hm⟩ := (cos_eq_one_iff _).mp h1
  have hpi : 0 < 2 * π := by positivity
  rw [← hm, abs_mul, abs_of_pos hpi] at hφ
  have hm1 : |(m : ℝ)| < 1 := by
    by_contra hc'
    push Not at hc'
    nlinarith
  have hm0 : m = 0 := by
    have h2 := abs_lt.mp hm1
    have a1 : (-1 : ℤ) < m := by exact_mod_cast h2.1
    have a2 : m < 1 := by exact_mod_cast h2.2
    omega
  rw [hm0] at hm
  simp at hm
  linarith

/-! ### The motion in time -/

/-- The velocity after the eccentric anomaly advances by `φ`: the rate of `keplerPos` divided
by the rate `(1 - ε cos(E₀ + φ))/n` of `keplerTime`. -/
noncomputable def keplerVel (μ : ℝ) (r v : V3) (φ : ℝ) : V3 :=
  ((1 - eCos μ r v * cos φ + eSin μ r v * sin φ) / meanMotion μ r v)⁻¹ •
    ((-(semimajor μ r v / norm r * sin φ)) • r +
      ((norm r / semimajor μ r v * cos φ + eSin μ r v * sin φ) / meanMotion μ r v) • v)

/-- The advance of the eccentric anomaly at the time `τ`: the inverse of `keplerTime`. -/
noncomputable def keplerAdvance (μ : ℝ) (r v : V3) (τ : ℝ) : ℝ :=
  Function.invFun (keplerTime μ r v) τ

/-- The rates along one coordinate.  With `F = f p + g q`, the rate `G = D⁻¹ (f' p + g' q)`,
and the rate `D = (1 - A cos φ + B sin φ)/n` of Kepler's time, `F' = f' p + g' q` and
`G' = -F/(n D²)`. -/
theorem kepler_component {a n n1 A B p q : ℝ} (ha : a ≠ 0) (hn : n ≠ 0) (hn1 : n1 ≠ 0)
    (hA : A = 1 - n1 / a) {φ : ℝ} (hD : 1 - A * cos φ + B * sin φ ≠ 0) :
    HasDerivAt (fun φ => (1 - a / n1 * (1 - cos φ)) * p +
        (n1 / a * sin φ + B * (1 - cos φ)) / n * q)
      ((-(a / n1 * sin φ)) * p + (n1 / a * cos φ + B * sin φ) / n * q) φ ∧
    HasDerivAt (fun φ => ((1 - A * cos φ + B * sin φ) / n)⁻¹ *
        ((-(a / n1 * sin φ)) * p + (n1 / a * cos φ + B * sin φ) / n * q))
      (-((1 - a / n1 * (1 - cos φ)) * p + (n1 / a * sin φ + B * (1 - cos φ)) / n * q) /
        (n * ((1 - A * cos φ + B * sin φ) / n) ^ 2)) φ := by
  have hc := hasDerivAt_cos φ
  have hs := hasDerivAt_sin φ
  constructor
  · have h1 := (((hc.const_sub 1).const_mul (a / n1)).const_sub 1).mul_const p
    have h2 := ((((hs.const_mul (n1 / a)).fun_add ((hc.const_sub 1).const_mul B)).div_const
      n)).mul_const q
    exact (h1.fun_add h2).congr_deriv (by ring)
  · have hD' : (1 - A * cos φ + B * sin φ) / n ≠ 0 := div_ne_zero hD hn
    have dD := (((hc.const_mul A).const_sub 1).fun_add (hs.const_mul B)).div_const n
    have dH := ((hs.const_mul (a / n1)).fun_neg.mul_const p).fun_add
      ((((hc.const_mul (n1 / a)).fun_add (hs.const_mul B)).div_const n).mul_const q)
    refine ((dD.fun_inv hD').fun_mul dH).congr_deriv ?_
    have hsq := sin_sq_add_cos_sq φ
    set D := (1 - A * cos φ + B * sin φ) / n with hDdef
    set H := (-(a / n1 * sin φ)) * p + (n1 / a * cos φ + B * sin φ) / n * q with hH
    set F := (1 - a / n1 * (1 - cos φ)) * p + (n1 / a * sin φ + B * (1 - cos φ)) / n * q with hF
    have key : (-(a / n1 * cos φ) * p + (n1 / a * -sin φ + B * cos φ) / n * q) * D -
        H * ((-(A * -sin φ) + B * cos φ) / n) = -F / n := by
      have h1 : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
      have h2 : n1 * n1⁻¹ = 1 := mul_inv_cancel₀ hn1
      rw [hDdef, hH, hF, hA]
      linear_combination (p * a * (1 - n1 / a) / (n1 * n) - q * B / n ^ 2) * hsq +
        (-(p * n⁻¹)) * h1 + (-(p * n⁻¹ * a * a⁻¹)) * h2
    have e : -((-(A * -sin φ) + B * cos φ) / n) / D ^ 2 * H +
        D⁻¹ * (-(a / n1 * cos φ) * p + (n1 / a * -sin φ + B * cos φ) / n * q) =
        ((-(a / n1 * cos φ) * p + (n1 / a * -sin φ + B * cos φ) / n * q) * D -
          H * ((-(A * -sin φ) + B * cos φ) / n)) / D ^ 2 := by
      field_simp
      ring
    rw [e, key]
    field_simp

theorem keplerTime_hasDerivAt (μ : ℝ) (r v : V3) (φ : ℝ) :
    HasDerivAt (keplerTime μ r v)
      ((1 - eCos μ r v * cos φ + eSin μ r v * sin φ) / meanMotion μ r v) φ := by
  have hc := hasDerivAt_cos φ
  have hs := hasDerivAt_sin φ
  have h := ((((hasDerivAt_id φ).fun_add (hc.const_mul (-eSin μ r v))).fun_sub
    (hs.const_mul (eCos μ r v))).add_const (eSin μ r v)).div_const (meanMotion μ r v)
  exact h.congr_deriv (by ring)

section Motion

variable {μ : ℝ} {r v : V3} (hμ : 0 < μ) (hr : 0 < norm r) (he : 0 < 2 / norm r - dot v v / μ)
  (hh : 0 < dot (cross r v) (cross r v))
include hμ hr he hh

theorem keplerTime_surjective : Function.Surjective (keplerTime μ r v) := by
  obtain ⟨-, hn, -, -, -, -, -, hε⟩ := kepler_basics hμ hr he hh
  intro τ
  obtain ⟨φ, hφ⟩ := Sgp4.Kepler.lhs_surjective (a := eCos μ r v) (b := -eSin μ r v)
    (by rw [neg_sq]; exact hε) (τ * meanMotion μ r v - eSin μ r v)
  exact ⟨φ, by rw [keplerTime, hφ]; field_simp; ring⟩

theorem keplerTime_advance (τ : ℝ) : keplerTime μ r v (keplerAdvance μ r v τ) = τ :=
  Function.invFun_eq (keplerTime_surjective hμ hr he hh τ)

theorem keplerAdvance_time (φ : ℝ) : keplerAdvance μ r v (keplerTime μ r v φ) = φ :=
  Function.leftInverse_invFun (keplerTime_strictMono hμ hr he hh).injective φ

theorem keplerAdvance_zero : keplerAdvance μ r v 0 = 0 := by
  have := keplerAdvance_time hμ hr he hh 0
  rwa [keplerTime_zero] at this

theorem keplerAdvance_strictMono : StrictMono (keplerAdvance μ r v) := by
  intro τ1 τ2 h
  have hm := keplerTime_strictMono hμ hr he hh
  rw [← hm.lt_iff_lt, keplerTime_advance hμ hr he hh, keplerTime_advance hμ hr he hh]
  exact h

theorem keplerAdvance_hasDerivAt (τ : ℝ) :
    HasDerivAt (keplerAdvance μ r v)
      ((1 - eCos μ r v * cos (keplerAdvance μ r v τ) + eSin μ r v * sin (keplerAdvance μ r v τ)) /
        meanMotion μ r v)⁻¹ τ := by
  obtain ⟨-, hn, -, -, -, -, -, hε⟩ := kepler_basics hμ hr he hh
  have hcont : Continuous (keplerAdvance μ r v) :=
    (keplerAdvance_strictMono hμ hr he hh).monotone.continuous_of_surjective
      fun φ => ⟨keplerTime μ r v φ, keplerAdvance_time hμ hr he hh φ⟩
  have hD : 0 < 1 - eCos μ r v * cos (keplerAdvance μ r v τ) +
      eSin μ r v * sin (keplerAdvance μ r v τ) := by
    have := combo_lt_one hε (sin_sq_add_cos_sq (keplerAdvance μ r v τ)); linarith
  exact HasDerivAt.of_local_left_inverse hcont.continuousAt
    (keplerTime_hasDerivAt μ r v _) (div_pos hD hn).ne'
    (Filter.Eventually.of_forall (keplerTime_advance hμ hr he hh))

theorem keplerVel_zero : keplerVel μ r v 0 = v := by
  obtain ⟨ha, hn, -, -, -, -, -, -⟩ := kepler_basics hμ hr he hh
  have h1 : 1 - eCos μ r v = norm r / semimajor μ r v := by rw [eCos]; ring
  ext <;> simp only [keplerVel, cos_zero, sin_zero, mul_one, mul_zero, add_zero, neg_zero,
    smul_x, smul_y, smul_z, add_x, add_y, add_z, zero_mul, h1] <;> field_simp <;> ring

/-- **The motion along an elliptic orbit solves Newton's equation.**  The position
`keplerPos` and the velocity `keplerVel` at the advance of the eccentric anomaly that Kepler's
equation gives for each time are a solution of `r'' = -μ r/|r|³` that is at the state `(r, v)`
at the time 0. -/
theorem kepler_newton :
    Newton μ (fun τ => keplerPos μ r v (keplerAdvance μ r v τ))
      (fun τ => keplerVel μ r v (keplerAdvance μ r v τ)) ∧
      keplerPos μ r v (keplerAdvance μ r v 0) = r ∧
      keplerVel μ r v (keplerAdvance μ r v 0) = v := by
  obtain ⟨ha, hn, hn2, -, -, -, -, hε⟩ := kepler_basics hμ hr he hh
  have hA : eCos μ r v = 1 - norm r / semimajor μ r v := rfl
  have hD : ∀ φ, 0 < 1 - eCos μ r v * cos φ + eSin μ r v * sin φ := fun φ => by
    have := combo_lt_one hε (sin_sq_add_cos_sq φ); linarith
  have hΦ := keplerAdvance_hasDerivAt hμ hr he hh
  have hrad := kepler_radius hμ hr he hh
  have pos : ∀ τ, 0 < norm (keplerPos μ r v (keplerAdvance μ r v τ)) := fun τ => by
    rw [hrad]; exact mul_pos ha (hD _)
  have dpos : ∀ (p q : ℝ) (τ : ℝ),
      HasDerivAt (fun s => (1 - semimajor μ r v / norm r * (1 - cos (keplerAdvance μ r v s))) * p +
          (norm r / semimajor μ r v * sin (keplerAdvance μ r v s) +
            eSin μ r v * (1 - cos (keplerAdvance μ r v s))) / meanMotion μ r v * q)
        (((1 - eCos μ r v * cos (keplerAdvance μ r v τ) +
            eSin μ r v * sin (keplerAdvance μ r v τ)) / meanMotion μ r v)⁻¹ *
          ((-(semimajor μ r v / norm r * sin (keplerAdvance μ r v τ))) * p +
            (norm r / semimajor μ r v * cos (keplerAdvance μ r v τ) +
              eSin μ r v * sin (keplerAdvance μ r v τ)) / meanMotion μ r v * q)) τ :=
    fun p q τ => (((kepler_component (p := p) (q := q) ha.ne' hn.ne' hr.ne' hA
      (hD (keplerAdvance μ r v τ)).ne').1).comp τ (hΦ τ)).congr_deriv (by ring)
  have dvel : ∀ (p q : ℝ) (τ : ℝ),
      HasDerivAt (fun s => ((1 - eCos μ r v * cos (keplerAdvance μ r v s) +
            eSin μ r v * sin (keplerAdvance μ r v s)) / meanMotion μ r v)⁻¹ *
          ((-(semimajor μ r v / norm r * sin (keplerAdvance μ r v s))) * p +
            (norm r / semimajor μ r v * cos (keplerAdvance μ r v s) +
              eSin μ r v * sin (keplerAdvance μ r v s)) / meanMotion μ r v * q))
        (-μ * ((1 - semimajor μ r v / norm r * (1 - cos (keplerAdvance μ r v τ))) * p +
            (norm r / semimajor μ r v * sin (keplerAdvance μ r v τ) +
              eSin μ r v * (1 - cos (keplerAdvance μ r v τ))) / meanMotion μ r v * q) /
          norm (keplerPos μ r v (keplerAdvance μ r v τ)) ^ 3) τ := by
    intro p q τ
    refine (((kepler_component (p := p) (q := q) ha.ne' hn.ne' hr.ne' hA
      (hD (keplerAdvance μ r v τ)).ne').2).comp τ (hΦ τ)).congr_deriv ?_
    have hDτ := hD (keplerAdvance μ r v τ)
    rw [hrad]
    generalize keplerAdvance μ r v τ = φ at hDτ ⊢
    generalize eCos μ r v = A at hDτ ⊢
    generalize eSin μ r v = B at hDτ ⊢
    generalize semimajor μ r v = a at ha hn2 ⊢
    generalize meanMotion μ r v = n at hn hn2 ⊢
    subst hn2
    field_simp
  refine ⟨⟨pos, dpos r.x v.x, dpos r.y v.y, dpos r.z v.z, dvel r.x v.x, dvel r.y v.y,
    dvel r.z v.z⟩, ?_, ?_⟩
  · rw [keplerAdvance_zero hμ hr he hh, keplerPos_zero]
  · rw [keplerAdvance_zero hμ hr he hh, keplerVel_zero hμ hr he hh]

end Motion

end Demos.Orbit
