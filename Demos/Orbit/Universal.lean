import Demos.Orbit.Newton
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
The motion along a two-body orbit of every conic, in the universal variable.  For a state
`(r, v)`, let `β = 2μ/|r| - |v|²`, which is `μ/a` for the semimajor axis `a` of an ellipse, 0 for a
parabola, and negative for a hyperbola.  The universal variable `χ` advances at the rate
`dχ/dt = 1/|r|`.  The universal functions `U0`, `U1`, `U2`, and `U3` of `β` and `χ` are
`cos(√β χ)`, `sin(√β χ)/√β`, `(1 - cos(√β χ))/β`, and `(χ - sin(√β χ)/√β)/β` for an ellipse, the
same with `cosh` and `sinh` of `√(-β) χ` for a hyperbola, and `1`, `χ`, `χ²/2`, and `χ³/6` for a
parabola.  For an ellipse, `√β χ` is the advance of the eccentric anomaly.

When the universal variable advances by `χ`, the position is `f r + g v` with Lagrange's
coefficients `f = 1 - μ U2/|r|` and `g = |r| U1 + (r · v) U2` (`conicPos`), its distance from the
origin is `R = |r| U0 + (r · v) U1 + μ U2` (`conicRadius`), and the time is
`|r| U1 + (r · v) U2 + μ U3` (`conicTime`): Kepler's equation for an ellipse, its hyperbolic
form for a hyperbola, and Barker's equation for a parabola.  The proofs of the path, the
distance, the time, and Newton's equation use only the derivatives `U0' = -β U1`, `U1' = U0`,
`U2' = U1`, and `U3' = U2` and the identities `U0 + β U2 = 1` and `U1² = U2 (1 + U0)`, which
hold for every conic.

`conicPos_onPath` states that each position lies on the path of the state's orbit at the distance
`R`, `conicTime_strictMono` that the time increases with `χ`, and `conicPos_inj` that the
positions at two advances `χ1` and `χ2` are distinct when `β ≤ 0`, or when `√β |χ1 - χ2| < 2π`.
`ConicTransfer` states that the motion first reaches a position after a given time.
`conic_newton` states that the position `conicPos` and the velocity `conicVel`, at the advance
`conicAdvance τ` that inverts the time, solve Newton's equation and are at `(r, v)` at the time 0.
-/

namespace Demos.Orbit

open V3 Real

/-! ### The universal functions -/

/-- `cos(√β χ)` for `β > 0`, `cosh(√(-β) χ)` for `β < 0`, and 1 for `β = 0`. -/
noncomputable def U0 (β χ : ℝ) : ℝ :=
  if 0 < β then cos (√β * χ) else if β < 0 then cosh (√(-β) * χ) else 1

/-- `sin(√β χ)/√β` for `β > 0`, `sinh(√(-β) χ)/√(-β)` for `β < 0`, and `χ` for `β = 0`. -/
noncomputable def U1 (β χ : ℝ) : ℝ :=
  if 0 < β then sin (√β * χ) / √β else if β < 0 then sinh (√(-β) * χ) / √(-β) else χ

/-- `(1 - U0)/β`, and `χ²/2` for `β = 0`. -/
noncomputable def U2 (β χ : ℝ) : ℝ := if β = 0 then χ ^ 2 / 2 else (1 - U0 β χ) / β

/-- `(χ - U1)/β`, and `χ³/6` for `β = 0`. -/
noncomputable def U3 (β χ : ℝ) : ℝ := if β = 0 then χ ^ 3 / 6 else (χ - U1 β χ) / β

theorem U0_pos {β : ℝ} (h : 0 < β) (χ : ℝ) : U0 β χ = cos (√β * χ) := ite_eq_left h

theorem U0_neg {β : ℝ} (h : β < 0) (χ : ℝ) : U0 β χ = cosh (√(-β) * χ) := by
  rw [U0, ite_eq_right (not_lt.mpr h.le), ite_eq_left h]

theorem U0_zero (χ : ℝ) : U0 0 χ = 1 := by simp [U0]

theorem U1_pos {β : ℝ} (h : 0 < β) (χ : ℝ) : U1 β χ = sin (√β * χ) / √β := ite_eq_left h

theorem U1_neg {β : ℝ} (h : β < 0) (χ : ℝ) : U1 β χ = sinh (√(-β) * χ) / √(-β) := by
  rw [U1, ite_eq_right (not_lt.mpr h.le), ite_eq_left h]

theorem U1_zero (χ : ℝ) : U1 0 χ = χ := by simp [U1]

theorem U0_add_U2 (β χ : ℝ) : U0 β χ + β * U2 β χ = 1 := by
  rcases eq_or_ne β 0 with h | h
  · subst h; rw [U0_zero]; ring
  · rw [U2, ite_eq_right h]; field_simp; ring

theorem U1_add_U3 (β χ : ℝ) : U1 β χ + β * U3 β χ = χ := by
  rcases eq_or_ne β 0 with h | h
  · subst h; rw [U1_zero]; ring
  · rw [U3, ite_eq_right h]; field_simp; ring

/-- `U1² = U2 (1 + U0)`. -/
theorem U1_sq (β χ : ℝ) : U1 β χ ^ 2 = U2 β χ * (1 + U0 β χ) := by
  rcases lt_trichotomy β 0 with h | h | h
  · have hw2 : √(-β) ^ 2 = -β := sq_sqrt (by linarith)
    rw [U2, ite_eq_right h.ne, U0_neg h, U1_neg h, div_pow, hw2,
      show (1 - cosh (√(-β) * χ)) / β * (1 + cosh (√(-β) * χ)) =
        (1 - cosh (√(-β) * χ) ^ 2) / β by ring, cosh_sq]
    ring
  · subst h; rw [U2, ite_eq_left rfl, U0_zero, U1_zero]; ring
  · have hw2 : √β ^ 2 = β := sq_sqrt h.le
    rw [U2, ite_eq_right h.ne', U0_pos h, U1_pos h, div_pow, hw2,
      show (1 - cos (√β * χ)) / β * (1 + cos (√β * χ)) = (1 - cos (√β * χ) ^ 2) / β by ring,
      sin_sq]

theorem U_zero (β : ℝ) : U0 β 0 = 1 ∧ U1 β 0 = 0 ∧ U2 β 0 = 0 ∧ U3 β 0 = 0 := by
  have h0 : U0 β 0 = 1 := by unfold U0; split_ifs <;> simp
  have h1 : U1 β 0 = 0 := by unfold U1; split_ifs <;> simp
  refine ⟨h0, h1, ?_, ?_⟩
  · unfold U2; split_ifs <;> simp [h0]
  · unfold U3; split_ifs <;> simp [h1]

theorem U0_hasDerivAt (β χ : ℝ) : HasDerivAt (U0 β) (-β * U1 β χ) χ := by
  rcases lt_trichotomy β 0 with h | h | h
  · have hw2 : √(-β) ^ 2 = -β := sq_sqrt (by linarith)
    have hw : √(-β) ≠ 0 := (sqrt_pos.mpr (by linarith)).ne'
    rw [show U0 β = fun χ => cosh (√(-β) * χ) from funext (U0_neg h), U1_neg h]
    refine ((hasDerivAt_id' χ).const_mul (√(-β))).cosh.congr_deriv ?_
    linear_combination (norm := skip) (sinh (√(-β) * χ) / √(-β)) * hw2
    field_simp
    ring
  · subst h
    rw [show U0 0 = fun _ => (1 : ℝ) from funext U0_zero]
    exact (hasDerivAt_const χ (1 : ℝ)).congr_deriv (by ring)
  · have hw2 : √β ^ 2 = β := sq_sqrt h.le
    have hw : √β ≠ 0 := (sqrt_pos.mpr h).ne'
    rw [show U0 β = fun χ => cos (√β * χ) from funext (U0_pos h), U1_pos h]
    refine ((hasDerivAt_id' χ).const_mul √β).cos.congr_deriv ?_
    linear_combination (norm := skip) (-sin (√β * χ) / √β) * hw2
    field_simp
    ring

theorem U1_hasDerivAt (β χ : ℝ) : HasDerivAt (U1 β) (U0 β χ) χ := by
  rcases lt_trichotomy β 0 with h | h | h
  · have hw : √(-β) ≠ 0 := (sqrt_pos.mpr (by linarith)).ne'
    rw [show U1 β = fun χ => sinh (√(-β) * χ) / √(-β) from funext (U1_neg h), U0_neg h]
    refine (((hasDerivAt_id' χ).const_mul (√(-β))).sinh.div_const _).congr_deriv ?_
    field_simp
  · subst h
    rw [show U1 0 = fun χ => χ from funext U1_zero, U0_zero]
    exact hasDerivAt_id' χ
  · have hw : √β ≠ 0 := (sqrt_pos.mpr h).ne'
    rw [show U1 β = fun χ => sin (√β * χ) / √β from funext (U1_pos h), U0_pos h]
    refine (((hasDerivAt_id' χ).const_mul √β).sin.div_const _).congr_deriv ?_
    field_simp

theorem U2_hasDerivAt (β χ : ℝ) : HasDerivAt (U2 β) (U1 β χ) χ := by
  rcases eq_or_ne β 0 with h | h
  · subst h
    rw [show U2 0 = fun χ => χ ^ 2 / 2 from funext fun χ => ite_eq_left rfl, U1_zero]
    exact ((hasDerivAt_pow 2 χ).div_const 2).congr_deriv (by ring)
  · rw [show U2 β = fun χ => (1 - U0 β χ) / β from funext fun χ => ite_eq_right h]
    exact (((U0_hasDerivAt β χ).const_sub 1).div_const β).congr_deriv (by field_simp)

theorem U3_hasDerivAt (β χ : ℝ) : HasDerivAt (U3 β) (U2 β χ) χ := by
  rcases eq_or_ne β 0 with h | h
  · subst h
    rw [show U3 0 = fun χ => χ ^ 3 / 6 from funext fun χ => ite_eq_left rfl,
      show U2 0 χ = χ ^ 2 / 2 from ite_eq_left rfl]
    exact ((hasDerivAt_pow 3 χ).div_const 6).congr_deriv (by ring)
  · rw [show U3 β = fun χ => (χ - U1 β χ) / β from funext fun χ => ite_eq_right h, U2,
      ite_eq_right h]
    exact (((hasDerivAt_id' χ).fun_sub (U1_hasDerivAt β χ)).div_const β).congr_deriv rfl

/-- For `β ≤ 0`, `U1` increases strictly. -/
theorem U1_strictMono {β : ℝ} (h : β ≤ 0) : StrictMono (U1 β) := by
  rcases h.lt_or_eq with h | h
  · have hw : 0 < √(-β) := sqrt_pos.mpr (by linarith)
    intro a b hab
    rw [U1_neg h, U1_neg h]
    exact div_lt_div_of_pos_right (sinh_strictMono (mul_lt_mul_of_pos_left hab hw)) hw
  · subst h
    intro a b hab
    rwa [U1_zero, U1_zero]

/-! ### Vectors in the basis of a state -/

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

theorem dot_lin (e r v : V3) (f g : ℝ) : dot e (f • r + g • v) = f * dot e r + g * dot e v := by
  simp only [dot, add_x, add_y, add_z, smul_x, smul_y, smul_z]; ring

theorem smul_cancel {a b : ℝ} {h : V3} (hh : 0 < dot h h) (e : a • h = b • h) : a = b := by
  have := congrArg (dot h) e
  rw [dot_smul, dot_smul] at this
  exact mul_right_cancel₀ hh.ne' this

/-- The coefficients of a vector in the basis `r`, `v` of a state with `r × v ≠ 0` are unique. -/
theorem coeff_unique {r v : V3} (hh : 0 < dot (cross r v) (cross r v)) {a b a' b' : ℝ}
    (e : a • r + b • v = a' • r + b' • v) : a = a' ∧ b = b' := by
  have hb : b • cross r v = b' • cross r v := by
    have := congrArg (cross r) e
    rwa [cross_basis, cross_basis] at this
  have ha : (-a) • cross r v = (-a') • cross r v := by
    have := congrArg (cross v) e
    rwa [cross_basis_right, cross_basis_right] at this
  exact ⟨neg_inj.mp (smul_cancel hh ha), smul_cancel hh hb⟩

/-- `(a · b)² ≤ (a · a) (b · b)`. -/
theorem dot_sq_le (a b : V3) : dot a b ^ 2 ≤ dot a a * dot b b := by
  have : dot (cross a b) (cross a b) = dot a a * dot b b - dot a b ^ 2 := by
    simp only [dot, cross_x, cross_y, cross_z]; ring
  have := dot_self_nonneg (cross a b)
  linarith

/-! ### The motion -/

/-- `β = 2μ/|r| - |v|²`: `μ/a` for an ellipse with the semimajor axis `a`, 0 for a parabola, and
negative for a hyperbola. -/
noncomputable def conicBeta (μ : ℝ) (r v : V3) : ℝ := 2 * μ / norm r - dot v v

/-- The position after the universal variable advances by `χ`: `f r + g v` with Lagrange's
coefficients `f = 1 - μ U2/|r|` and `g = |r| U1 + (r · v) U2`. -/
noncomputable def conicPos (μ : ℝ) (r v : V3) (χ : ℝ) : V3 :=
  (1 - μ * U2 (conicBeta μ r v) χ / norm r) • r +
    (norm r * U1 (conicBeta μ r v) χ + dot r v * U2 (conicBeta μ r v) χ) • v

/-- The distance from the origin after the advance `χ`: `|r| U0 + (r · v) U1 + μ U2`. -/
noncomputable def conicRadius (μ : ℝ) (r v : V3) (χ : ℝ) : ℝ :=
  norm r * U0 (conicBeta μ r v) χ + dot r v * U1 (conicBeta μ r v) χ +
    μ * U2 (conicBeta μ r v) χ

/-- The time of the advance `χ`, the universal form of Kepler's equation:
`|r| U1 + (r · v) U2 + μ U3`. -/
noncomputable def conicTime (μ : ℝ) (r v : V3) (χ : ℝ) : ℝ :=
  norm r * U1 (conicBeta μ r v) χ + dot r v * U2 (conicBeta μ r v) χ +
    μ * U3 (conicBeta μ r v) χ

/-- The velocity after the advance `χ`: the rate of `conicPos` in `χ` divided by the rate
`conicRadius` of `conicTime`. -/
noncomputable def conicVel (μ : ℝ) (r v : V3) (χ : ℝ) : V3 :=
  (conicRadius μ r v χ)⁻¹ • ((-(μ * U1 (conicBeta μ r v) χ / norm r)) • r +
    (norm r * U0 (conicBeta μ r v) χ + dot r v * U1 (conicBeta μ r v) χ) • v)

/-- The motion from the state `(r, v)` along its conic first reaches `r'` after the time `t`:
`r × v ≠ 0`, and the universal variable advances by some `χ > 0` to the position `r'` in the time
`t`, with no position `r'` at a smaller positive advance.  Since the time increases with the
advance (`conicTime_strictMono`), `t` is the least positive time at which the motion is at
`r'`. -/
def ConicTransfer (μ : ℝ) (r v r' : V3) (t : ℝ) : Prop :=
  0 < dot (cross r v) (cross r v) ∧
    ∃ χ, 0 < χ ∧ conicPos μ r v χ = r' ∧ conicTime μ r v χ = t ∧
      ∀ χ', 0 < χ' → χ' < χ → conicPos μ r v χ' ≠ r'

theorem conicRadius_hasDerivAt (μ : ℝ) (r v : V3) (χ : ℝ) :
    HasDerivAt (conicRadius μ r v)
      (norm r * (-conicBeta μ r v * U1 (conicBeta μ r v) χ) +
        dot r v * U0 (conicBeta μ r v) χ + μ * U1 (conicBeta μ r v) χ) χ :=
  (((U0_hasDerivAt _ χ).const_mul (norm r)).fun_add
    ((U1_hasDerivAt _ χ).const_mul (dot r v))).fun_add ((U2_hasDerivAt _ χ).const_mul μ)

/-- The rate of the time in the advance is the distance `R`. -/
theorem conicTime_hasDerivAt (μ : ℝ) (r v : V3) (χ : ℝ) :
    HasDerivAt (conicTime μ r v) (conicRadius μ r v χ) χ :=
  (((U1_hasDerivAt _ χ).const_mul (norm r)).fun_add
    ((U2_hasDerivAt _ χ).const_mul (dot r v))).fun_add ((U3_hasDerivAt _ χ).const_mul μ)

section State

variable {μ : ℝ} {r v : V3}

theorem norm_pos_of_cross (hh : 0 < dot (cross r v) (cross r v)) : 0 < norm r := by
  rcases (norm_nonneg r).lt_or_eq with h | h
  · exact h
  · have h0 : dot r r = 0 := by rw [← norm_sq, ← h]; ring
    rw [eq_zero_of_dot_self h0] at hh
    simp [dot] at hh

theorem conicBeta_dot : dot v v = 2 * μ / norm r - conicBeta μ r v := by
  rw [conicBeta]; ring

theorem conic_zero : conicPos μ r v 0 = r ∧ conicTime μ r v 0 = 0 ∧
    conicRadius μ r v 0 = norm r := by
  obtain ⟨h0, h1, h2, h3⟩ := U_zero (conicBeta μ r v)
  refine ⟨?_, ?_, ?_⟩
  · ext <;> simp [conicPos, h1, h2]
  · simp [conicTime, h1, h2, h3]
  · simp [conicRadius, h0, h1, h2]

theorem conicVel_zero (hn : 0 < norm r) : conicVel μ r v 0 = v := by
  obtain ⟨h0, h1, -, -⟩ := U_zero (conicBeta μ r v)
  have hn0 := hn.ne'
  rw [conicVel, conic_zero.2.2, h0, h1]
  ext <;> simp <;> field_simp

/-- `|f r + g v|² = R²`. -/
theorem conicPos_dot_self (hn : 0 < norm r) (χ : ℝ) :
    dot (conicPos μ r v χ) (conicPos μ r v χ) = conicRadius μ r v χ ^ 2 := by
  have h0 := U0_add_U2 (conicBeta μ r v) χ
  have h1 := U1_sq (conicBeta μ r v) χ
  have hv := conicBeta_dot (μ := μ) (r := r) (v := v)
  rw [conicPos, dot_basis, ← norm_sq r, hv, conicRadius]
  generalize conicBeta μ r v = β at h0 h1 ⊢
  generalize U0 β χ = A at h0 h1 ⊢
  generalize U1 β χ = B at h0 h1 ⊢
  generalize U2 β χ = C at h0 h1 ⊢
  generalize dot r v = σ
  have hn0 := hn.ne'
  linear_combination (norm := (field_simp; ring))
    (norm r * (2 * μ - β * norm r) - σ ^ 2) * h1 +
      ((norm r * (2 * μ - β * norm r) - σ ^ 2) * C -
        norm r * (norm r * A + norm r * (1 - β * C) + 2 * σ * B + 2 * μ * C)) * h0

/-- The polar equation with `R` in place of `|f r + g v|`: `R + e · (f r + g v) = |h|²/μ`. -/
theorem conic_polar (hμ : 0 < μ) (hn : 0 < norm r) (χ : ℝ) :
    conicRadius μ r v χ + dot (orbitOf μ r v).e (conicPos μ r v χ) =
      dot (orbitOf μ r v).h (orbitOf μ r v).h / μ := by
  have h0 := U0_add_U2 (conicBeta μ r v) χ
  have hv := conicBeta_dot (μ := μ) (r := r) (v := v)
  have edr : dot (μ⁻¹ • cross v (cross r v) - (norm r)⁻¹ • r) r =
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
  have hl : dot (cross r v) (cross r v) = norm r ^ 2 * dot v v - dot r v ^ 2 := by
    rw [norm_sq]; simp only [dot, cross_x, cross_y, cross_z]; ring
  simp only [orbitOf, conicPos]
  rw [dot_lin, edr, edv, hl, hv, conicRadius]
  generalize conicBeta μ r v = β at h0 ⊢
  generalize U0 β χ = A at h0 ⊢
  generalize U1 β χ = B
  generalize U2 β χ = C at h0 ⊢
  generalize dot r v = σ
  have hn0 := hn.ne'
  have hμ0 := hμ.ne'
  linear_combination (norm := (field_simp; ring)) norm r * h0

variable (hμ : 0 < μ) (hh : 0 < dot (cross r v) (cross r v))
include hμ hh

theorem conicRadius_ne_zero (χ : ℝ) : conicRadius μ r v χ ≠ 0 := by
  have hn := norm_pos_of_cross hh
  intro h0
  have hd := conicPos_dot_self (μ := μ) (v := v) hn χ
  rw [h0, zero_pow two_ne_zero] at hd
  have hp := conic_polar (v := v) hμ hn χ
  rw [h0, eq_zero_of_dot_self hd] at hp
  have : dot (orbitOf μ r v).e 0 = 0 := by simp [dot]
  rw [this, add_zero] at hp
  have : 0 < dot (orbitOf μ r v).h (orbitOf μ r v).h / μ := div_pos hh hμ
  linarith

/-- The distance `R` is positive. -/
theorem conicRadius_pos (χ : ℝ) : 0 < conicRadius μ r v χ := by
  have hn := norm_pos_of_cross hh
  by_contra hneg
  have hlt : conicRadius μ r v χ < 0 :=
    lt_of_le_of_ne (not_lt.mp hneg) (conicRadius_ne_zero hμ hh χ)
  have hc : ContinuousOn (conicRadius μ r v) (Set.uIcc 0 χ) :=
    (continuous_iff_continuousAt.mpr fun χ =>
      (conicRadius_hasDerivAt μ r v χ).continuousAt).continuousOn
  have h0 : (0 : ℝ) ∈ Set.uIcc (conicRadius μ r v 0) (conicRadius μ r v χ) := by
    rw [conic_zero.2.2]
    exact Set.mem_uIcc.mpr (Or.inr ⟨hlt.le, hn.le⟩)
  obtain ⟨c, -, hc0⟩ := intermediate_value_uIcc hc h0
  exact conicRadius_ne_zero hμ hh c hc0

/-- `|f r + g v| = R`. -/
theorem conicPos_norm (χ : ℝ) : norm (conicPos μ r v χ) = conicRadius μ r v χ := by
  rw [V3.norm, conicPos_dot_self (norm_pos_of_cross hh), sqrt_sq (conicRadius_pos hμ hh χ).le]

/-- Each position of the motion lies on the path of the state's orbit. -/
theorem conicPos_onPath (χ : ℝ) : OnPath μ (orbitOf μ r v) (conicPos μ r v χ) := by
  have hn := norm_pos_of_cross hh
  refine ⟨hh, ?_, ?_, ?_⟩
  · rw [conicPos_norm hμ hh]; exact conicRadius_pos hμ hh χ
  · simp only [orbitOf, conicPos, dot, add_x, add_y, add_z, smul_x, smul_y, smul_z, cross_x,
      cross_y, cross_z]
    ring
  · rw [conicPos_norm hμ hh]; exact conic_polar hμ hn χ

/-- A lower bound of the distance: `|h|²/μ ≤ R (1 + |e|)`. -/
theorem conicRadius_ge (χ : ℝ) :
    dot (orbitOf μ r v).h (orbitOf μ r v).h / μ / (1 + norm (orbitOf μ r v).e) ≤
      conicRadius μ r v χ := by
  have hp := conic_polar hμ (norm_pos_of_cross hh) (v := v) χ
  have hR := conicRadius_pos hμ hh χ
  have hcs : dot (orbitOf μ r v).e (conicPos μ r v χ) ≤
      norm (orbitOf μ r v).e * conicRadius μ r v χ := by
    have hsq := dot_sq_le (orbitOf μ r v).e (conicPos μ r v χ)
    rw [← norm_sq, ← norm_sq, conicPos_norm hμ hh, ← mul_pow] at hsq
    exact (abs_le_of_sq_le_sq' hsq (mul_nonneg (norm_nonneg _) hR.le)).2
  rw [div_le_iff₀ (by have := norm_nonneg (orbitOf μ r v).e; linarith)]
  nlinarith

/-- The time increases with the advance. -/
theorem conicTime_strictMono : StrictMono (conicTime μ r v) :=
  strictMono_of_deriv_pos fun χ => by
    rw [(conicTime_hasDerivAt μ r v χ).deriv]; exact conicRadius_pos hμ hh χ

theorem conicTime_surjective : Function.Surjective (conicTime μ r v) := by
  set c := dot (orbitOf μ r v).h (orbitOf μ r v).h / μ / (1 + norm (orbitOf μ r v).e)
  have hc : 0 < c := div_pos (div_pos hh hμ) (by have := norm_nonneg (orbitOf μ r v).e; linarith)
  have hdiff : Differentiable ℝ (conicTime μ r v) := fun χ =>
    (conicTime_hasDerivAt μ r v χ).differentiableAt
  have hle : ∀ χ, c ≤ deriv (conicTime μ r v) χ := fun χ => by
    rw [(conicTime_hasDerivAt μ r v χ).deriv]; exact conicRadius_ge hμ hh χ
  have hmv := mul_sub_le_image_sub_of_le_deriv hdiff hle
  have h0 : conicTime μ r v 0 = 0 := conic_zero.2.1
  intro τ
  have hq : 0 ≤ |τ| / c := by positivity
  have ha : conicTime μ r v (-(|τ| / c) - 1) < τ := by
    have h1 := hmv (show -(|τ| / c) - 1 ≤ 0 by linarith)
    have h2 : c * (0 - (-(|τ| / c) - 1)) = |τ| + c := by field_simp; ring
    linarith [neg_abs_le τ]
  have hb : τ < conicTime μ r v (|τ| / c + 1) := by
    have h1 := hmv (show (0 : ℝ) ≤ |τ| / c + 1 by linarith)
    have h2 : c * (|τ| / c + 1 - 0) = |τ| + c := by field_simp; ring
    linarith [le_abs_self τ]
  obtain ⟨χ, -, hχ⟩ := intermediate_value_Icc (by linarith : -(|τ| / c) - 1 ≤ |τ| / c + 1)
    (continuous_iff_continuousAt.mpr fun χ =>
      (conicTime_hasDerivAt μ r v χ).continuousAt).continuousOn ⟨ha.le, hb.le⟩
  exact ⟨χ, hχ⟩

/-- The positions at two advances `χ1 ≠ χ2` are distinct when `β ≤ 0`, or when
`√β |χ1 - χ2| < 2π`. -/
theorem conicPos_inj {χ1 χ2 : ℝ}
    (hχ : conicBeta μ r v ≤ 0 ∨ √(conicBeta μ r v) * |χ1 - χ2| < 2 * π)
    (heq : conicPos μ r v χ1 = conicPos μ r v χ2) : χ1 = χ2 := by
  have hn := norm_pos_of_cross hh
  obtain ⟨hf, hg⟩ := coeff_unique hh heq
  have h2 : U2 (conicBeta μ r v) χ1 = U2 (conicBeta μ r v) χ2 := by
    have : μ * U2 (conicBeta μ r v) χ1 / norm r = μ * U2 (conicBeta μ r v) χ2 / norm r := by
      linarith
    exact mul_left_cancel₀ hμ.ne' ((div_left_inj' hn.ne').mp this)
  have h1 : U1 (conicBeta μ r v) χ1 = U1 (conicBeta μ r v) χ2 := by
    rw [h2] at hg
    exact mul_left_cancel₀ hn.ne' (by linarith)
  rcases le_or_gt (conicBeta μ r v) 0 with hb | hb
  · exact (U1_strictMono hb).injective h1
  · have hw : 0 < √(conicBeta μ r v) := sqrt_pos.mpr hb
    have hc : cos (√(conicBeta μ r v) * χ1) = cos (√(conicBeta μ r v) * χ2) := by
      have h0 := U0_add_U2 (conicBeta μ r v) χ1
      rw [h2, ← U0_add_U2 (conicBeta μ r v) χ2] at h0
      rw [← U0_pos hb, ← U0_pos hb]; linarith
    have hs : sin (√(conicBeta μ r v) * χ1) = sin (√(conicBeta μ r v) * χ2) := by
      rw [U1_pos hb, U1_pos hb] at h1
      exact (div_left_inj' hw.ne').mp h1
    have hcos : cos (√(conicBeta μ r v) * χ1 - √(conicBeta μ r v) * χ2) = 1 := by
      rw [cos_sub, hc, hs]
      linear_combination sin_sq_add_cos_sq (√(conicBeta μ r v) * χ2)
    obtain ⟨m, hm⟩ := (cos_eq_one_iff _).mp hcos
    have hlt : √(conicBeta μ r v) * |χ1 - χ2| < 2 * π := hχ.resolve_left (not_le.mpr hb)
    have hpi : 0 < 2 * π := by positivity
    have habs : |(m : ℝ)| * (2 * π) = √(conicBeta μ r v) * |χ1 - χ2| := by
      have e := congrArg abs hm
      rw [← mul_sub, abs_mul (m : ℝ), abs_mul (√(conicBeta μ r v)), abs_of_pos hpi,
        abs_of_pos hw] at e
      exact e
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
    simp only [Int.cast_zero, zero_mul] at hm
    have : √(conicBeta μ r v) * (χ1 - χ2) = 0 := by rw [mul_sub]; linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hw.ne'
    · linarith

/-! ### The motion in time -/

/-- The advance of the universal variable at the time `τ`: the inverse of `conicTime`. -/
noncomputable def conicAdvance (μ : ℝ) (r v : V3) (τ : ℝ) : ℝ :=
  Function.invFun (conicTime μ r v) τ

theorem conicTime_advance (τ : ℝ) : conicTime μ r v (conicAdvance μ r v τ) = τ :=
  Function.invFun_eq (conicTime_surjective hμ hh τ)

theorem conicAdvance_time (χ : ℝ) : conicAdvance μ r v (conicTime μ r v χ) = χ :=
  Function.leftInverse_invFun (conicTime_strictMono hμ hh).injective χ

theorem conicAdvance_zero : conicAdvance μ r v 0 = 0 := by
  have := conicAdvance_time hμ hh 0
  rwa [conic_zero.2.1] at this

theorem conicAdvance_strictMono : StrictMono (conicAdvance μ r v) := by
  intro τ1 τ2 h
  rw [← (conicTime_strictMono hμ hh).lt_iff_lt, conicTime_advance hμ hh,
    conicTime_advance hμ hh]
  exact h

theorem conicAdvance_hasDerivAt (τ : ℝ) :
    HasDerivAt (conicAdvance μ r v) (conicRadius μ r v (conicAdvance μ r v τ))⁻¹ τ := by
  have hcont : Continuous (conicAdvance μ r v) :=
    (conicAdvance_strictMono hμ hh).monotone.continuous_of_surjective
      fun χ => ⟨conicTime μ r v χ, conicAdvance_time hμ hh χ⟩
  exact HasDerivAt.of_local_left_inverse hcont.continuousAt
    (conicTime_hasDerivAt μ r v _) (conicRadius_ne_zero hμ hh _)
    (Filter.Eventually.of_forall (conicTime_advance hμ hh))

end State

/-- The rates along one coordinate.  With `F = f p + g q`, its rate `G = f' p + g' q` in `χ`, and
`R = n U0 + σ U1 + μ U2`, the rate of `R⁻¹ G` in `χ` is `-μ F/R²`. -/
theorem conic_component (β n σ μ p q χ : ℝ) (hn : n ≠ 0)
    (hR : n * U0 β χ + σ * U1 β χ + μ * U2 β χ ≠ 0) :
    HasDerivAt (fun χ => (1 - μ * U2 β χ / n) * p + (n * U1 β χ + σ * U2 β χ) * q)
      ((-(μ * U1 β χ / n)) * p + (n * U0 β χ + σ * U1 β χ) * q) χ ∧
    HasDerivAt (fun χ => (n * U0 β χ + σ * U1 β χ + μ * U2 β χ)⁻¹ *
        ((-(μ * U1 β χ / n)) * p + (n * U0 β χ + σ * U1 β χ) * q))
      (-μ * ((1 - μ * U2 β χ / n) * p + (n * U1 β χ + σ * U2 β χ) * q) /
        (n * U0 β χ + σ * U1 β χ + μ * U2 β χ) ^ 2) χ := by
  have d0 := U0_hasDerivAt β χ
  have d1 := U1_hasDerivAt β χ
  have d2 := U2_hasDerivAt β χ
  constructor
  · refine ((((d2.const_mul μ).div_const n).const_sub 1).mul_const p |>.fun_add
      (((d1.const_mul n).fun_add (d2.const_mul σ)).mul_const q)).congr_deriv ?_
    ring
  · have dR := ((d0.const_mul n).fun_add (d1.const_mul σ)).fun_add (d2.const_mul μ)
    have dG := (((d1.const_mul μ).div_const n).fun_neg.mul_const p).fun_add
      (((d0.const_mul n).fun_add (d1.const_mul σ)).mul_const q)
    refine ((dR.fun_inv hR).fun_mul dG).congr_deriv ?_
    have h0 := U0_add_U2 β χ
    have h1 := U1_sq β χ
    generalize U0 β χ = A at h0 h1 hR ⊢
    generalize U1 β χ = B at h0 h1 hR ⊢
    generalize U2 β χ = C at h0 h1 hR ⊢
    linear_combination (norm := (field_simp; ring))
      ((p * (μ ^ 2 / n - μ * β) - q * μ * σ) / (n * A + σ * B + μ * C) ^ 2) * h1 +
        ((-(p * μ * (1 + A)) - q * μ * n * B) / (n * A + σ * B + μ * C) ^ 2) * h0

section Newton

variable {μ : ℝ} {r v : V3} (hμ : 0 < μ) (hh : 0 < dot (cross r v) (cross r v))
include hμ hh

/-- **The motion along a conic solves Newton's equation.**  The position `conicPos` and the
velocity `conicVel` at the advance that `conicTime` gives for each time are a solution of
`r'' = -μ r/|r|³` that is at the state `(r, v)` at the time 0. -/
theorem conic_newton :
    Newton μ (fun τ => conicPos μ r v (conicAdvance μ r v τ))
      (fun τ => conicVel μ r v (conicAdvance μ r v τ)) ∧
      conicPos μ r v (conicAdvance μ r v 0) = r ∧
      conicVel μ r v (conicAdvance μ r v 0) = v := by
  have hn := norm_pos_of_cross hh
  have hΦ := conicAdvance_hasDerivAt hμ hh
  have hR := fun χ => conicRadius_ne_zero hμ hh (v := v) χ
  have dpos : ∀ (p q τ : ℝ),
      HasDerivAt (fun s => (1 - μ * U2 (conicBeta μ r v) (conicAdvance μ r v s) / norm r) * p +
          (norm r * U1 (conicBeta μ r v) (conicAdvance μ r v s) +
            dot r v * U2 (conicBeta μ r v) (conicAdvance μ r v s)) * q)
        ((conicRadius μ r v (conicAdvance μ r v τ))⁻¹ *
          ((-(μ * U1 (conicBeta μ r v) (conicAdvance μ r v τ) / norm r)) * p +
            (norm r * U0 (conicBeta μ r v) (conicAdvance μ r v τ) +
              dot r v * U1 (conicBeta μ r v) (conicAdvance μ r v τ)) * q)) τ :=
    fun p q τ => (((conic_component (conicBeta μ r v) (norm r) (dot r v) μ p q _ hn.ne'
      (hR _)).1).comp τ (hΦ τ)).congr_deriv (by ring)
  have dvel : ∀ (p q τ : ℝ),
      HasDerivAt (fun s => (conicRadius μ r v (conicAdvance μ r v s))⁻¹ *
          ((-(μ * U1 (conicBeta μ r v) (conicAdvance μ r v s) / norm r)) * p +
            (norm r * U0 (conicBeta μ r v) (conicAdvance μ r v s) +
              dot r v * U1 (conicBeta μ r v) (conicAdvance μ r v s)) * q))
        (-μ * ((1 - μ * U2 (conicBeta μ r v) (conicAdvance μ r v τ) / norm r) * p +
            (norm r * U1 (conicBeta μ r v) (conicAdvance μ r v τ) +
              dot r v * U2 (conicBeta μ r v) (conicAdvance μ r v τ)) * q) /
          norm (conicPos μ r v (conicAdvance μ r v τ)) ^ 3) τ := by
    intro p q τ
    refine (((conic_component (conicBeta μ r v) (norm r) (dot r v) μ p q _ hn.ne'
      (hR _)).2).comp τ (hΦ τ)).congr_deriv ?_
    rw [conicPos_norm hμ hh]
    have := hR (conicAdvance μ r v τ)
    unfold conicRadius at this ⊢
    field_simp
  refine ⟨⟨fun τ => by rw [conicPos_norm hμ hh]; exact conicRadius_pos hμ hh _,
    dpos r.x v.x, dpos r.y v.y, dpos r.z v.z, dvel r.x v.x, dvel r.y v.y, dvel r.z v.z⟩, ?_, ?_⟩
  · rw [conicAdvance_zero hμ hh, conic_zero.1]
  · rw [conicAdvance_zero hμ hh, conicVel_zero hn]

end Newton

end Demos.Orbit
