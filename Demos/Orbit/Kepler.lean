import Demos.Orbit.TwoBody
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
time `t`: the orbit is an ellipse, and the eccentric anomaly advances by some `φ` with
`0 < φ < 2π` to the position `r'` in the time `t` of Kepler's equation.  `keplerPos_inj` makes
`φ` the only advance in `[0, 2π)` that reaches `r'`, and `keplerTime_strictMono` makes `t` the
least positive time at which the motion is at `r'`. -/
def EllipticTransfer (μ : ℝ) (r v r' : V3) (t : ℝ) : Prop :=
  0 < 2 / norm r - dot v v / μ ∧
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
  have hm := Sgp4.Kepler.lhs_strictMono (a := eCos μ r v) (b := -eSin μ r v) (by rw [neg_sq]; exact hε)
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

end Demos.Orbit
