import Demos.Avoidance.Spec
import Demos.Orbit.Newton
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.MonotoneContinuity

/-!
The two-body propagation of the model.  `propagate_newton` (M2) states that the position and
velocity of `t ↦ propagate mu r v t` solve Newton's equation `r'' = -μ r/|r|³` at every time, in
the sense of `Demos.Orbit.Newton`, for a state with `α > 0` and `e² < 1`, and `propagate_zero`
(M1) that the propagation starts at the state.  The proof differentiates the root of Kepler's
equation as the inverse of its left side (`root_hasDerivAt`), then the coefficients `f`, `g`,
`ḟ`, and `ġ`, and shows that the length of the position is `w/α`.
-/

open Real Filter Demos.Sgp4 Demos.Orbit Demos.Orbit.V3

namespace Demos.Avoidance

/-! ### The root of Kepler's equation as a function of its right side -/

theorem lhs_hasDerivAt (a b E : ℝ) :
    HasDerivAt (Kepler.lhs a b) (1 - b * sin E - a * cos E) E := by
  have h := ((hasDerivAt_id' E).add ((hasDerivAt_cos E).const_mul b)).sub
    ((hasDerivAt_sin E).const_mul a)
  exact h.congr_deriv (by ring)

theorem slope_lhs_pos {a b : ℝ} (h : a ^ 2 + b ^ 2 < 1) (E : ℝ) :
    0 < 1 - b * sin E - a * cos E := by
  have h1 := (abs_le.mp (Kepler.combination_le a b E)).2
  have h2 := Kepler.slope_pos h
  linarith

theorem root_lhs {a b : ℝ} (h : a ^ 2 + b ^ 2 < 1) (E : ℝ) :
    Kepler.root a b (Kepler.lhs a b E) = E :=
  (Kepler.lhs_strictMono h).injective (Kepler.root_spec h _)

theorem root_continuous {a b : ℝ} (h : a ^ 2 + b ^ 2 < 1) : Continuous (Kepler.root a b) := by
  apply Monotone.continuous_of_surjective
  · intro u v huv
    by_contra hlt
    have := Kepler.lhs_strictMono h (not_le.mp hlt)
    rw [Kepler.root_spec h, Kepler.root_spec h] at this
    linarith
  · intro E
    exact ⟨_, root_lhs h E⟩

/-- The derivative of the root of `E + b cos E - a sin E = u` with respect to `u`. -/
theorem root_hasDerivAt {a b : ℝ} (h : a ^ 2 + b ^ 2 < 1) (u : ℝ) :
    HasDerivAt (Kepler.root a b)
      (1 - b * sin (Kepler.root a b u) - a * cos (Kepler.root a b u))⁻¹ u :=
  HasDerivAt.of_local_left_inverse (root_continuous h).continuousAt (lhs_hasDerivAt a b _)
    (slope_lhs_pos h _).ne' (Eventually.of_forall fun v => Kepler.root_spec h v)

/-! ### The coefficients as functions of time

For a state with `|r₀| = R0`, `r₀ · v₀ = D`, `α`, and `q = √(α/μ)`, the change of the eccentric
anomaly after `t` seconds is `anomalyAt`, and `fAt`, `gAt`, `fdAt`, and `gdAt` are the
coefficients of `propagate`. -/

section Coefficients

variable (mu R0 D alpha q : ℝ)

noncomputable def anomalyAt (t : ℝ) : ℝ :=
  keplerRoot (1 - R0 * alpha) (-(D * q)) (mu * alpha * q * t + -(D * q))

noncomputable def wAt (t : ℝ) : ℝ :=
  1 - (1 - R0 * alpha) * cos (anomalyAt mu R0 D alpha q t) -
    -(D * q) * sin (anomalyAt mu R0 D alpha q t)

noncomputable def fAt (t : ℝ) : ℝ := 1 - (1 - cos (anomalyAt mu R0 D alpha q t)) / (R0 * alpha)

noncomputable def gAt (t : ℝ) : ℝ :=
  (R0 * alpha * sin (anomalyAt mu R0 D alpha q t) +
    D * q * (1 - cos (anomalyAt mu R0 D alpha q t))) / (mu * alpha * q)

noncomputable def fdAt (t : ℝ) : ℝ :=
  -(alpha * sin (anomalyAt mu R0 D alpha q t)) / (q * wAt mu R0 D alpha q t * R0)

noncomputable def gdAt (t : ℝ) : ℝ :=
  1 - (1 - cos (anomalyAt mu R0 D alpha q t)) / wAt mu R0 D alpha q t

variable {mu R0 D alpha q}

theorem wAt_pos (he : (1 - R0 * alpha) ^ 2 + (-(D * q)) ^ 2 < 1) (t : ℝ) :
    0 < wAt mu R0 D alpha q t := by
  have := slope_lhs_pos he (anomalyAt mu R0 D alpha q t)
  unfold wAt
  linarith

theorem anomalyAt_hasDerivAt (he : (1 - R0 * alpha) ^ 2 + (-(D * q)) ^ 2 < 1) (t : ℝ) :
    HasDerivAt (anomalyAt mu R0 D alpha q) (mu * alpha * q / wAt mu R0 D alpha q t) t := by
  have h1 := root_hasDerivAt he (mu * alpha * q * t + -(D * q))
  have h2 : HasDerivAt (fun t => mu * alpha * q * t + -(D * q)) (mu * alpha * q) t :=
    (((hasDerivAt_id' t).const_mul (mu * alpha * q)).add_const (-(D * q))).congr_deriv (by ring)
  have h3 := h1.comp t h2
  unfold anomalyAt keplerRoot
  refine h3.congr_deriv ?_
  unfold wAt anomalyAt keplerRoot
  rw [div_eq_inv_mul]
  ring

/-- The derivatives of `sin E` and of `w`, with `E' = n/w`. -/
theorem sin_hasDerivAt (he : (1 - R0 * alpha) ^ 2 + (-(D * q)) ^ 2 < 1) (t : ℝ) :
    HasDerivAt (fun t => sin (anomalyAt mu R0 D alpha q t))
      (cos (anomalyAt mu R0 D alpha q t) * (mu * alpha * q / wAt mu R0 D alpha q t)) t :=
  (anomalyAt_hasDerivAt (mu := mu) he t).sin

theorem cos_hasDerivAt (he : (1 - R0 * alpha) ^ 2 + (-(D * q)) ^ 2 < 1) (t : ℝ) :
    HasDerivAt (fun t => cos (anomalyAt mu R0 D alpha q t))
      (-sin (anomalyAt mu R0 D alpha q t) * (mu * alpha * q / wAt mu R0 D alpha q t)) t :=
  (anomalyAt_hasDerivAt (mu := mu) he t).cos

theorem wAt_hasDerivAt (he : (1 - R0 * alpha) ^ 2 + (-(D * q)) ^ 2 < 1) (t : ℝ) :
    HasDerivAt (wAt mu R0 D alpha q)
      (mu * alpha * q / wAt mu R0 D alpha q t *
        ((1 - R0 * alpha) * sin (anomalyAt mu R0 D alpha q t) +
          -(D * q) * -cos (anomalyAt mu R0 D alpha q t))) t := by
  have h := ((cos_hasDerivAt (mu := mu) he t).const_mul (1 - R0 * alpha)).const_sub 1 |>.sub
    ((sin_hasDerivAt (mu := mu) he t).const_mul (-(D * q)))
  exact h.congr_deriv (by ring)

/-- `ḟ` is the derivative of `f`. -/
theorem fAt_hasDerivAt (hR : 0 < R0) (ha : 0 < alpha) (hq : 0 < q)
    (hm : mu = alpha / (q * q)) (he : (1 - R0 * alpha) ^ 2 + (-(D * q)) ^ 2 < 1) (t : ℝ) :
    HasDerivAt (fAt mu R0 D alpha q) (fdAt mu R0 D alpha q t) t := by
  have h := ((cos_hasDerivAt (mu := mu) he t).const_sub 1).div_const (R0 * alpha) |>.const_sub 1
  refine h.congr_deriv ?_
  have hw := (wAt_pos (mu := mu) he t).ne'
  have := hR.ne'
  have := ha.ne'
  have := hq.ne'
  unfold fdAt
  subst hm
  field_simp

/-- `ġ` is the derivative of `g`. -/
theorem gAt_hasDerivAt (hR : 0 < R0) (ha : 0 < alpha) (hq : 0 < q)
    (hm : mu = alpha / (q * q)) (he : (1 - R0 * alpha) ^ 2 + (-(D * q)) ^ 2 < 1) (t : ℝ) :
    HasDerivAt (gAt mu R0 D alpha q) (gdAt mu R0 D alpha q t) t := by
  have h := (((sin_hasDerivAt (mu := mu) he t).const_mul (R0 * alpha)).add
    (((cos_hasDerivAt (mu := mu) he t).const_sub 1).const_mul (D * q))).div_const (mu * alpha * q)
  refine h.congr_deriv ?_
  have hw := (wAt_pos (mu := mu) he t).ne'
  have hmu : 0 < mu := by rw [hm]; positivity
  have := hmu.ne'
  have := hR.ne'
  have := ha.ne'
  have := hq.ne'
  have hg : gdAt mu R0 D alpha q t =
      (R0 * alpha * cos (anomalyAt mu R0 D alpha q t) +
        D * q * sin (anomalyAt mu R0 D alpha q t)) / wAt mu R0 D alpha q t := by
    unfold gdAt
    rw [eq_div_iff hw, sub_mul, div_mul_cancel₀ _ hw]
    unfold wAt
    ring
  rw [hg]
  field_simp

/-- The derivative of `sin E / w`, reduced with `sin² E + cos² E = 1`. -/
theorem sinw_hasDerivAt (he : (1 - R0 * alpha) ^ 2 + (-(D * q)) ^ 2 < 1) (t : ℝ) :
    HasDerivAt (fun t => sin (anomalyAt mu R0 D alpha q t) / wAt mu R0 D alpha q t)
      (mu * alpha * q / wAt mu R0 D alpha q t *
        (cos (anomalyAt mu R0 D alpha q t) - (1 - R0 * alpha)) /
          wAt mu R0 D alpha q t ^ 2) t := by
  have hw := (wAt_pos (mu := mu) he t).ne'
  have h := (sin_hasDerivAt (mu := mu) he t).div (wAt_hasDerivAt (mu := mu) he t) hw
  refine h.congr_deriv ?_
  rw [div_left_inj' (pow_ne_zero 2 hw)]
  have hwd : wAt mu R0 D alpha q t = 1 - (1 - R0 * alpha) * cos (anomalyAt mu R0 D alpha q t) -
      -(D * q) * sin (anomalyAt mu R0 D alpha q t) := rfl
  linear_combination (mu * alpha * q / wAt mu R0 D alpha q t *
      cos (anomalyAt mu R0 D alpha q t)) * hwd +
    (-(1 - R0 * alpha) * (mu * alpha * q / wAt mu R0 D alpha q t)) *
      sin_sq_add_cos_sq (anomalyAt mu R0 D alpha q t)

/-- The derivative of `(1 - cos E) / w`, reduced with `sin² E + cos² E = 1`. -/
theorem versw_hasDerivAt (he : (1 - R0 * alpha) ^ 2 + (-(D * q)) ^ 2 < 1) (t : ℝ) :
    HasDerivAt (fun t => (1 - cos (anomalyAt mu R0 D alpha q t)) / wAt mu R0 D alpha q t)
      (mu * alpha * q / wAt mu R0 D alpha q t *
        (R0 * alpha * sin (anomalyAt mu R0 D alpha q t) +
          D * q * (1 - cos (anomalyAt mu R0 D alpha q t))) / wAt mu R0 D alpha q t ^ 2) t := by
  have hw := (wAt_pos (mu := mu) he t).ne'
  have h := ((cos_hasDerivAt (mu := mu) he t).const_sub 1).div (wAt_hasDerivAt (mu := mu) he t) hw
  refine h.congr_deriv ?_
  rw [div_left_inj' (pow_ne_zero 2 hw)]
  have hwd : wAt mu R0 D alpha q t = 1 - (1 - R0 * alpha) * cos (anomalyAt mu R0 D alpha q t) -
      -(D * q) * sin (anomalyAt mu R0 D alpha q t) := rfl
  linear_combination (mu * alpha * q / wAt mu R0 D alpha q t *
      sin (anomalyAt mu R0 D alpha q t)) * hwd +
    ((D * q) * (mu * alpha * q / wAt mu R0 D alpha q t)) *
      sin_sq_add_cos_sq (anomalyAt mu R0 D alpha q t)

/-- The derivative of `ḟ` is `-μ f α³ / w³`. -/
theorem fdAt_hasDerivAt (hR : 0 < R0) (ha : 0 < alpha) (hq : 0 < q)
    (he : (1 - R0 * alpha) ^ 2 + (-(D * q)) ^ 2 < 1) (t : ℝ) :
    HasDerivAt (fdAt mu R0 D alpha q)
      (-mu * fAt mu R0 D alpha q t / (wAt mu R0 D alpha q t / alpha) ^ 3) t := by
  have hw := (wAt_pos (mu := mu) he t).ne'
  have h := (sinw_hasDerivAt (mu := mu) he t).const_mul (-(alpha / (q * R0)))
  have e : fdAt mu R0 D alpha q =
      fun t => -(alpha / (q * R0)) *
        (sin (anomalyAt mu R0 D alpha q t) / wAt mu R0 D alpha q t) := by
    funext s
    unfold fdAt
    ring
  rw [e]
  refine h.congr_deriv ?_
  have := hR.ne'
  have := ha.ne'
  have := hq.ne'
  unfold fAt
  field_simp
  ring

/-- The derivative of `ġ` is `-μ g α³ / w³`. -/
theorem gdAt_hasDerivAt (hR : 0 < R0) (ha : 0 < alpha) (hq : 0 < q)
    (hm : mu = alpha / (q * q)) (he : (1 - R0 * alpha) ^ 2 + (-(D * q)) ^ 2 < 1) (t : ℝ) :
    HasDerivAt (gdAt mu R0 D alpha q)
      (-mu * gAt mu R0 D alpha q t / (wAt mu R0 D alpha q t / alpha) ^ 3) t := by
  have hw := (wAt_pos (mu := mu) he t).ne'
  have h := (versw_hasDerivAt (mu := mu) he t).const_sub 1
  refine h.congr_deriv ?_
  have := hR.ne'
  have := ha.ne'
  have := hq.ne'
  unfold gAt
  subst hm
  field_simp

/-- The length of the position: `|f r₀ + g v₀|² = (w/α)²` when `|r₀|² = R0²`, `r₀ · v₀ = D`, and
`|v₀|² = μ (2/R0 - α)`. -/
theorem norm_identity (hR : 0 < R0) (ha : 0 < alpha) (hq : 0 < q) (hm : mu = alpha / (q * q))
    (t : ℝ) :
    fAt mu R0 D alpha q t ^ 2 * R0 ^ 2 + 2 * fAt mu R0 D alpha q t * gAt mu R0 D alpha q t * D +
        gAt mu R0 D alpha q t ^ 2 * (mu * (2 / R0 - alpha)) =
      (wAt mu R0 D alpha q t / alpha) ^ 2 := by
  have key : fAt mu R0 D alpha q t ^ 2 * R0 ^ 2 +
      2 * fAt mu R0 D alpha q t * gAt mu R0 D alpha q t * D +
        gAt mu R0 D alpha q t ^ 2 * (mu * (2 / R0 - alpha)) - (wAt mu R0 D alpha q t / alpha) ^ 2 =
      (2 * (R0 * alpha) - (R0 * alpha) ^ 2 - (D * q) ^ 2) / alpha ^ 2 *
        (sin (anomalyAt mu R0 D alpha q t) ^ 2 + cos (anomalyAt mu R0 D alpha q t) ^ 2 - 1) := by
    have := hR.ne'
    have := ha.ne'
    have := hq.ne'
    unfold fAt gAt wAt
    subst hm
    field_simp
    ring
  rw [sin_sq_add_cos_sq, sub_self, mul_zero, sub_eq_zero] at key
  exact key

end Coefficients

/-! ### The propagation -/

/-- The position and velocity of `propagate` as vectors. -/
noncomputable def stateAt (mu : ℝ) (r v : V3) (t : ℝ) : V3 × V3 :=
  let p := propagate mu r.x r.y r.z v.x v.y v.z t
  (⟨p.1, p.2.1, p.2.2.1⟩, ⟨p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩)

/-- The quantities of a state that `propagate` uses. -/
noncomputable def radius (r : V3) : ℝ := √(r.x * r.x + r.y * r.y + r.z * r.z)

noncomputable def alphaOf (mu : ℝ) (r v : V3) : ℝ :=
  2 / radius r - (v.x * v.x + v.y * v.y + v.z * v.z) / mu

noncomputable def qOf (mu : ℝ) (r v : V3) : ℝ := √(alphaOf mu r v / mu)

theorem stateAt_eq (mu : ℝ) (r v : V3) (t : ℝ) :
    stateAt mu r v t =
      (fAt mu (radius r) (dot r v) (alphaOf mu r v) (qOf mu r v) t • r +
          gAt mu (radius r) (dot r v) (alphaOf mu r v) (qOf mu r v) t • v,
        fdAt mu (radius r) (dot r v) (alphaOf mu r v) (qOf mu r v) t • r +
          gdAt mu (radius r) (dot r v) (alphaOf mu r v) (qOf mu r v) t • v) := rfl

theorem shape_eq (mu : ℝ) (r v : V3) :
    shape mu r.x r.y r.z v.x v.y v.z =
      (alphaOf mu r v, (1 - radius r * alphaOf mu r v) * (1 - radius r * alphaOf mu r v) +
        -(dot r v * qOf mu r v) * -(dot r v * qOf mu r v)) := rfl

/-- The facts that a bound state with `e² < 1` gives the coefficients. -/
theorem bound_facts {mu : ℝ} {r v : V3} (hmu : 0 < mu) (ha : 0 < (shape mu r.x r.y r.z v.x v.y v.z).1)
    (he : (shape mu r.x r.y r.z v.x v.y v.z).2 < 1) :
    0 < radius r ∧ 0 < alphaOf mu r v ∧ 0 < qOf mu r v ∧
      mu = alphaOf mu r v / (qOf mu r v * qOf mu r v) ∧
      (1 - radius r * alphaOf mu r v) ^ 2 + (-(dot r v * qOf mu r v)) ^ 2 < 1 ∧
      radius r ^ 2 = dot r r ∧
      dot v v = mu * (2 / radius r - alphaOf mu r v) := by
  simp only [shape_eq] at ha he
  have hR0 : 0 ≤ radius r := Real.sqrt_nonneg _
  have hR : 0 < radius r := by
    rcases hR0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hV : 0 ≤ v.x * v.x + v.y * v.y + v.z * v.z := by
        nlinarith [mul_self_nonneg v.x, mul_self_nonneg v.y, mul_self_nonneg v.z]
      have : alphaOf mu r v ≤ 0 := by
        unfold alphaOf
        rw [← h, div_zero, zero_sub, neg_nonpos]
        exact div_nonneg hV hmu.le
      linarith
  have hq : 0 < qOf mu r v := Real.sqrt_pos.mpr (div_pos ha hmu)
  have hqq : qOf mu r v * qOf mu r v = alphaOf mu r v / mu :=
    Real.mul_self_sqrt (div_pos ha hmu).le
  have hr2 : radius r ^ 2 = dot r r := by
    have hP : 0 ≤ r.x * r.x + r.y * r.y + r.z * r.z := by
      nlinarith [mul_self_nonneg r.x, mul_self_nonneg r.y, mul_self_nonneg r.z]
    unfold radius dot
    exact Real.sq_sqrt hP
  have := hmu.ne'
  have := ha.ne'
  refine ⟨hR, ha, hq, ?_, by simpa only [sq] using he, hr2, ?_⟩
  · rw [hqq]
    field_simp
  · unfold alphaOf dot
    field_simp
    ring

/-- **M1.**  The propagation of a bound state with `e² < 1` starts at the state. -/
theorem propagate_zero {mu : ℝ} {r v : V3} (hmu : 0 < mu)
    (ha : 0 < (shape mu r.x r.y r.z v.x v.y v.z).1)
    (he : (shape mu r.x r.y r.z v.x v.y v.z).2 < 1) :
    stateAt mu r v 0 = (r, v) := by
  obtain ⟨hR, hal, hq, -, hk, -, -⟩ := bound_facts hmu ha he
  have h0 : anomalyAt mu (radius r) (dot r v) (alphaOf mu r v) (qOf mu r v) 0 = 0 := by
    unfold anomalyAt keplerRoot
    have := root_lhs hk 0
    simp only [Kepler.lhs, cos_zero, sin_zero, mul_zero, mul_one, zero_add, sub_zero] at this
    simpa using this
  rw [stateAt_eq]
  simp only [fAt, gAt, fdAt, gdAt, h0, cos_zero, sin_zero, sub_self, zero_div, sub_zero,
    mul_zero, add_zero, neg_zero]
  refine Prod.ext ?_ ?_ <;> ext <;> simp

/-- **M2.**  For `μ > 0` and a state with `α > 0` and `e² < 1`, the position and velocity of the
propagation solve Newton's two-body equation at every time. -/
theorem propagate_newton {mu : ℝ} {r v : V3} (hmu : 0 < mu)
    (ha : 0 < (shape mu r.x r.y r.z v.x v.y v.z).1)
    (he : (shape mu r.x r.y r.z v.x v.y v.z).2 < 1) :
    Newton mu (fun t => (stateAt mu r v t).1) (fun t => (stateAt mu r v t).2) := by
  obtain ⟨hR, hal, hq, hm, hk, hr2, hv2⟩ := bound_facts hmu ha he
  set R0 := radius r with hR0
  set D := dot r v with hD
  set al := alphaOf mu r v with hal0
  set q := qOf mu r v with hq0
  have hnorm : ∀ t, V3.norm (stateAt mu r v t).1 = wAt mu R0 D al q t / al := by
    intro t
    simp only [stateAt_eq]
    have hid := norm_identity (D := D) hR hal hq hm t
    have hd : V3.dot (fAt mu R0 D al q t • r + gAt mu R0 D al q t • v)
        (fAt mu R0 D al q t • r + gAt mu R0 D al q t • v) =
        fAt mu R0 D al q t ^ 2 * R0 ^ 2 + 2 * fAt mu R0 D al q t * gAt mu R0 D al q t * D +
          gAt mu R0 D al q t ^ 2 * (mu * (2 / R0 - al)) := by
      rw [hr2, ← hv2, hD]
      simp only [V3.dot, V3.add_x, V3.add_y, V3.add_z, V3.smul_x, V3.smul_y, V3.smul_z]
      ring
    unfold V3.norm
    rw [hd, hid, Real.sqrt_sq (div_pos (wAt_pos (mu := mu) hk t) hal).le]
  have hpos : ∀ t, 0 < V3.norm (stateAt mu r v t).1 := fun t => by
    rw [hnorm]; exact div_pos (wAt_pos (mu := mu) hk t) hal
  have hf := fun t => fAt_hasDerivAt (D := D) hR hal hq hm hk t
  have hg := fun t => gAt_hasDerivAt (D := D) hR hal hq hm hk t
  have hfd := fun t => fdAt_hasDerivAt (mu := mu) (D := D) hR hal hq hk t
  have hgd := fun t => gdAt_hasDerivAt (D := D) hR hal hq hm hk t
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simp only [stateAt_eq, V3.add_x, V3.smul_x]
    exact ((hf t).mul_const r.x).add ((hg t).mul_const v.x)
  · intro t
    simp only [stateAt_eq, V3.add_y, V3.smul_y]
    exact ((hf t).mul_const r.y).add ((hg t).mul_const v.y)
  · intro t
    simp only [stateAt_eq, V3.add_z, V3.smul_z]
    exact ((hf t).mul_const r.z).add ((hg t).mul_const v.z)
  · intro t
    rw [hnorm]
    simp only [stateAt_eq, V3.add_x, V3.smul_x]
    exact (((hfd t).mul_const r.x).add ((hgd t).mul_const v.x)).congr_deriv (by ring)
  · intro t
    rw [hnorm]
    simp only [stateAt_eq, V3.add_y, V3.smul_y]
    exact (((hfd t).mul_const r.y).add ((hgd t).mul_const v.y)).congr_deriv (by ring)
  · intro t
    rw [hnorm]
    simp only [stateAt_eq, V3.add_z, V3.smul_z]
    exact (((hfd t).mul_const r.z).add ((hgd t).mul_const v.z)).congr_deriv (by ring)

#print axioms propagate_zero
#print axioms propagate_newton

end Demos.Avoidance
