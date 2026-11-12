import LeanExe.ProofKit.RealErf
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
The chi-square distribution.  `chiSquare k` is Mathlib's Gamma distribution with shape `k/2` and
rate `1/2`, `cdf k` its distribution function, and `tail k x` the probability of `(x, ∞)`.  For
`x ≥ 0` and `y = x/2`, `cdf_two`, `cdf_one`, and `cdf_add_two` give `1 - exp(-y)`, `erf(√y)`, and
the recurrence `cdf (k + 2) x = cdf k x - term (k/2) y`, with `term a y = exp(-y) y^a / Γ(a + 1)`,
from which `tail_closed` states the tail as `closedTail k y`.  `cdf k` is zero at zero, continuous,
and strictly increasing on `[0, ∞)`, and `quantileIn_of` turns a point below `p` and a point at or
above `p` into the unique quantile at `p` between them.
-/

namespace Demos.Gate.Model

open Real MeasureTheory Set ProbabilityTheory LeanExe.ProofKit

/-- The chi-square distribution with `k` degrees of freedom. -/
noncomputable def chiSquare (k : ℕ) : Measure ℝ := gammaMeasure ((k : ℝ) / 2) (1 / 2)

/-- The distribution function of the chi-square distribution. -/
noncomputable def cdf (k : ℕ) (x : ℝ) : ℝ := ProbabilityTheory.cdf (chiSquare k) x

/-- The probability that a chi-square variable exceeds `x`. -/
noncomputable def tail (k : ℕ) (x : ℝ) : ℝ := (chiSquare k).real (Ioi x)

/-- `exp(-y) y^a / Γ(a + 1)`, the difference of the distribution functions with shapes `a` and
`a + 1` at `2y`. -/
noncomputable def term (a y : ℝ) : ℝ := exp (-y) * y ^ a / Gamma (a + 1)

/-- The closed form of the tail at `x = 2y`. -/
noncomputable def closedTail (k : ℕ) (y : ℝ) : ℝ :=
  (if k % 2 = 1 then 1 - RealErf.erf (√y) else 0) +
    ∑ j ∈ Finset.range (k / 2), term (((k % 2 : ℕ) : ℝ) / 2 + j) y

theorem continuous_erf : Continuous RealErf.erf :=
  continuous_iff_continuousAt.mpr fun x => (RealErf.hasDerivAt_erf x).continuousAt

/-! ### The Gamma distribution with rate `1/2` -/

/-- The distribution function of the Gamma distribution with shape `a` and rate `1/2`. -/
noncomputable def G (a x : ℝ) : ℝ := ProbabilityTheory.cdf (gammaMeasure a (1 / 2)) x

theorem integrable_pdf {a : ℝ} (ha : 0 < a) : Integrable (gammaPDFReal a (1 / 2)) := by
  refine ⟨(measurable_gammaPDFReal a _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (gammaPDFReal_nonneg ha (by norm_num)))]
  have h := lintegral_gammaPDF_eq_one ha (by norm_num : (0 : ℝ) < 1 / 2)
  simp only [gammaPDF] at h
  rw [h]
  exact ENNReal.one_lt_top

theorem pdf_neg {a t : ℝ} (ht : t < 0) : gammaPDFReal a (1 / 2) t = 0 := by
  simp [gammaPDFReal, not_le.mpr ht]

theorem integral_Iic_zero {a : ℝ} : ∫ t in Iic (0 : ℝ), gammaPDFReal a (1 / 2) t = 0 := by
  rw [integral_Iic_eq_integral_Iio]
  exact setIntegral_eq_zero_of_forall_eq_zero fun t ht => pdf_neg ht

theorem G_eq_integral {a x : ℝ} (ha : 0 < a) (_hx : 0 ≤ x) :
    G a x = ∫ t in (0 : ℝ)..x, gammaPDFReal a (1 / 2) t := by
  have hI := integrable_pdf ha
  rw [G, cdf_gammaMeasure_eq_integral ha (by norm_num), ← intervalIntegral.integral_Iic_sub_Iic
    hI.integrableOn hI.integrableOn, integral_Iic_zero, sub_zero]

theorem G_neg {a x : ℝ} (ha : 0 < a) (hx : x < 0) : G a x = 0 := by
  rw [G, cdf_gammaMeasure_eq_integral ha (by norm_num)]
  exact setIntegral_eq_zero_of_forall_eq_zero fun t ht => pdf_neg (lt_of_le_of_lt ht hx)

theorem pdf_eq {a t : ℝ} (ht : 0 ≤ t) :
    gammaPDFReal a (1 / 2) t = exp (-(t / 2)) * (t / 2) ^ (a - 1) / (2 * Gamma a) := by
  have h1 : (t / 2) ^ (a - 1) = t ^ (a - 1) * (1 / 2) ^ (a - 1) := by
    rw [div_eq_mul_one_div t 2, mul_rpow ht (by norm_num)]
  have h2 : ((1 : ℝ) / 2) ^ a = (1 / 2) ^ (a - 1) * (1 / 2) := by
    rw [← rpow_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), sub_add_cancel]
  simp only [gammaPDFReal, ite_eq_left ht, h1, h2]
  rw [show -(1 / 2 * t) = -(t / 2) by ring]
  ring

/-- The derivative of `term a (t/2)` in `t`, for `t > 0`. -/
theorem hasDerivAt_term {a t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => term a (t / 2))
      ((exp (-(t / 2)) * ((t / 2) ^ (a - 1) * a) - exp (-(t / 2)) * (t / 2) ^ a) / 2 /
        Gamma (a + 1)) t := by
  have hd : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := (hasDerivAt_id t).div_const 2
  have he : HasDerivAt (fun t : ℝ => exp (-(t / 2))) (exp (-(t / 2)) * (-(1 / 2))) t :=
    (hd.neg).exp
  have hp : HasDerivAt (fun t : ℝ => (t / 2) ^ a) (1 / 2 * a * (t / 2) ^ (a - 1)) t :=
    hd.rpow_const (Or.inl (by positivity))
  refine ((he.mul hp).div_const (Gamma (a + 1))).congr_deriv ?_
  ring

theorem term_zero_point {a : ℝ} (ha : 0 < a) : term a 0 = 0 := by
  simp [term, zero_rpow ha.ne']

theorem continuous_term {a : ℝ} (ha : 0 < a) : Continuous fun t : ℝ => term a (t / 2) := by
  unfold term
  refine Continuous.div_const (Continuous.mul (by fun_prop) ?_) _
  exact (continuous_rpow_const ha.le).comp (by fun_prop)

theorem intervalIntegrable_pdf {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    IntervalIntegrable (gammaPDFReal a (1 / 2)) volume x y :=
  (integrable_pdf ha).intervalIntegrable

/-- The recurrence of the distribution functions in the shape. -/
theorem G_succ {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    G (a + 1) x = G a x - term a (x / 2) := by
  have ha1 : 0 < a + 1 := by linarith
  have hd : ∀ t ∈ Ioo 0 x, HasDerivAt (fun t => -term a (t / 2))
      (gammaPDFReal (a + 1) (1 / 2) t - gammaPDFReal a (1 / 2) t) t := by
    intro t ht
    have h0 : 0 < t := ht.1
    rw [pdf_eq h0.le, pdf_eq h0.le, add_sub_cancel_right]
    refine (hasDerivAt_term (a := a) h0).neg.congr_deriv ?_
    rw [Gamma_add_one ha.ne']
    field_simp
    ring
  have hint : IntervalIntegrable
      (fun t => gammaPDFReal (a + 1) (1 / 2) t - gammaPDFReal a (1 / 2) t) volume 0 x :=
    (intervalIntegrable_pdf ha1 0 x).sub (intervalIntegrable_pdf ha 0 x)
  have hcont : ContinuousOn (fun t => -term a (t / 2)) (Icc 0 x) :=
    (continuous_term ha).neg.continuousOn
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun t => -term a (t / 2)) hx hcont hd hint
  rw [intervalIntegral.integral_sub (intervalIntegrable_pdf ha1 0 x)
    (intervalIntegrable_pdf ha 0 x)] at hftc
  simp only [zero_div, term_zero_point ha, neg_zero, sub_zero] at hftc
  rw [G_eq_integral ha1 hx, G_eq_integral ha hx]
  linarith

theorem G_one {x : ℝ} (hx : 0 ≤ x) : G 1 x = 1 - exp (-(x / 2)) := by
  have hint := intervalIntegrable_pdf (a := 1) one_pos 0 x
  have hd : ∀ t ∈ Ioo 0 x, HasDerivAt (fun t : ℝ => -exp (-(t / 2)))
      (gammaPDFReal 1 (1 / 2) t) t := by
    intro t ht
    rw [pdf_eq ht.1.le, sub_self, rpow_zero, Gamma_one]
    refine (((hasDerivAt_id' t).div_const 2).neg.exp).neg.congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
    (by fun_prop : Continuous fun t : ℝ => -exp (-(t / 2))).continuousOn hd hint
  rw [G_eq_integral one_pos hx, hftc]
  simp
  ring

theorem G_half {x : ℝ} (hx : 0 ≤ x) : G (1 / 2) x = RealErf.erf (√(x / 2)) := by
  have hint := intervalIntegrable_pdf (a := 1 / 2) (by norm_num) 0 x
  have hcont : Continuous fun t : ℝ => RealErf.erf (√(t / 2)) :=
    continuous_erf.comp (by fun_prop)
  have hd : ∀ t ∈ Ioo 0 x, HasDerivAt (fun t : ℝ => RealErf.erf (√(t / 2)))
      (gammaPDFReal (1 / 2) (1 / 2) t) t := by
    intro t ht
    have h0 : 0 < t := ht.1
    have hs : 0 < √(t / 2) := Real.sqrt_pos.mpr (by positivity)
    have hq : HasDerivAt (fun t : ℝ => √(t / 2)) (1 / 2 / (2 * √(t / 2))) t :=
      ((hasDerivAt_id t).div_const 2).sqrt (by positivity)
    have := (RealErf.hasDerivAt_erf (√(t / 2))).comp t hq
    refine this.congr_deriv ?_
    rw [pdf_eq h0.le, Real.Gamma_one_half_eq, RealErf.scale, Real.sq_sqrt (by positivity)]
    have hr : (t / 2) ^ ((1 : ℝ) / 2 - 1) = (√(t / 2))⁻¹ := by
      rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, rpow_neg (by positivity),
        ← Real.sqrt_eq_rpow]
    rw [hr]
    have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
    field_simp
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx hcont.continuousOn hd hint
  rw [G_eq_integral (by norm_num) hx, hftc]
  simp [RealErf.erf_zero]

/-! ### The chi-square distribution -/

theorem cdf_eq_G (k : ℕ) (x : ℝ) : cdf k x = G ((k : ℝ) / 2) x := rfl

theorem shape_pos {k : ℕ} (hk : 1 ≤ k) : 0 < (k : ℝ) / 2 := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

instance isProbability {k : ℕ} [h : Fact (1 ≤ k)] : IsProbabilityMeasure (chiSquare k) :=
  isProbabilityMeasure_gammaMeasure (shape_pos h.out) (by norm_num)

theorem isProbability_of {k : ℕ} (hk : 1 ≤ k) : IsProbabilityMeasure (chiSquare k) :=
  isProbabilityMeasure_gammaMeasure (shape_pos hk) (by norm_num)

/-- The tail is one less the distribution function. -/
theorem tail_eq_one_sub {k : ℕ} (hk : 1 ≤ k) (x : ℝ) : tail k x = 1 - cdf k x := by
  have := isProbability_of hk
  rw [tail, cdf, ProbabilityTheory.cdf_eq_real, ← compl_Iic, measureReal_compl measurableSet_Iic,
    probReal_univ]

theorem cdf_neg {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x < 0) : cdf k x = 0 :=
  G_neg (shape_pos hk) hx

theorem cdf_zero {k : ℕ} (hk : 1 ≤ k) : cdf k 0 = 0 := by
  rw [cdf_eq_G, G_eq_integral (shape_pos hk) le_rfl, intervalIntegral.integral_same]

theorem cdf_two {x : ℝ} (hx : 0 ≤ x) : cdf 2 x = 1 - exp (-(x / 2)) := by
  rw [cdf_eq_G, show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num, G_one hx]

theorem cdf_one {x : ℝ} (hx : 0 ≤ x) : cdf 1 x = RealErf.erf (√(x / 2)) := by
  rw [cdf_eq_G, show ((1 : ℕ) : ℝ) / 2 = 1 / 2 by norm_num, G_half hx]

theorem cdf_add_two {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    cdf (k + 2) x = cdf k x - term ((k : ℝ) / 2) (x / 2) := by
  rw [cdf_eq_G, cdf_eq_G, show ((k + 2 : ℕ) : ℝ) / 2 = (k : ℝ) / 2 + 1 by push_cast; ring,
    G_succ (shape_pos hk) hx]

theorem shape_eq (k : ℕ) : (k : ℝ) / 2 = ((k % 2 : ℕ) : ℝ) / 2 + ((k / 2 : ℕ) : ℝ) := by
  have h := Nat.mod_add_div k 2
  have h' : (k : ℝ) = ((k % 2 : ℕ) : ℝ) + 2 * ((k / 2 : ℕ) : ℝ) := by exact_mod_cast h.symm
  rw [h']
  ring

theorem closedTail_add_two (k : ℕ) (y : ℝ) :
    closedTail (k + 2) y = closedTail k y + term ((k : ℝ) / 2) y := by
  unfold closedTail
  rw [show (k + 2) % 2 = k % 2 by omega, show (k + 2) / 2 = k / 2 + 1 by omega,
    Finset.sum_range_succ, shape_eq k]
  ring

/-- The closed form of the tail. -/
theorem tail_closed {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    tail k x = closedTail k (x / 2) := by
  have key : ∀ m : ℕ, tail (2 * m + 1) x = closedTail (2 * m + 1) (x / 2) ∧
      tail (2 * m + 2) x = closedTail (2 * m + 2) (x / 2) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [tail_eq_one_sub le_rfl, cdf_one hx]
        simp [closedTail]
      · rw [tail_eq_one_sub (by norm_num), cdf_two hx]
        simp [closedTail, term, Gamma_one]
    | succ m ih =>
      refine ⟨?_, ?_⟩
      · rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, tail_eq_one_sub (by omega),
          cdf_add_two (by omega) hx, closedTail_add_two, ← ih.1, tail_eq_one_sub (by omega)]
        ring
      · rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by ring, tail_eq_one_sub (by omega),
          cdf_add_two (by omega) hx, closedTail_add_two, ← ih.2, tail_eq_one_sub (by omega)]
        ring
  obtain ⟨m, rfl | rfl⟩ : ∃ m, k = 2 * m + 1 ∨ k = 2 * m + 2 :=
    ⟨(k - 1) / 2, by omega⟩
  · exact (key m).1
  · exact (key m).2

theorem tail_nonneg (k : ℕ) (x : ℝ) : 0 ≤ tail k x := measureReal_nonneg

theorem tail_le_one {k : ℕ} (hk : 1 ≤ k) (x : ℝ) : tail k x ≤ 1 := by
  have := isProbability_of hk
  exact measureReal_le_one

/-! ### The terms -/

theorem term_nonneg {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) : 0 ≤ term a y := by
  unfold term
  have := Gamma_pos_of_pos (by linarith : 0 < a + 1)
  positivity

theorem term_succ {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) :
    term (a + 1) y = term a y * y / (a + 1) := by
  unfold term
  rw [show a + 1 + 1 = (a + 1) + 1 by ring, Gamma_add_one (by linarith : a + 1 ≠ 0),
    rpow_add_one' hy (by linarith : a + 1 ≠ 0)]
  have := Gamma_pos_of_pos (by linarith : 0 < a + 1)
  field_simp

theorem term_zero_shape (y : ℝ) : term 0 y = exp (-y) := by
  simp [term, Gamma_one]

theorem term_half (y : ℝ) : term (1 / 2) y = 2 * exp (-y) * √(y / π) := by
  unfold term
  rw [show (1 : ℝ) / 2 + 1 = 1 / 2 + 1 by rfl, Gamma_add_one (by norm_num), Gamma_one_half_eq,
    ← Real.sqrt_eq_rpow, Real.sqrt_div' y pi_pos.le]
  have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
  field_simp

/-- A term with half-integer shape `k/2`, `k ≥ 1`, is at most 1, as the difference of two tails. -/
theorem term_le_one {k : ℕ} (hk : 1 ≤ k) {y : ℝ} (hy : 0 ≤ y) : term ((k : ℝ) / 2) y ≤ 1 := by
  have h2 : 0 ≤ 2 * y := by linarith
  have e := cdf_add_two hk h2
  rw [show 2 * y / 2 = y by ring] at e
  have t1 := tail_eq_one_sub (k := k + 2) (by omega) (2 * y)
  have t2 := tail_eq_one_sub hk (2 * y)
  have b1 := tail_nonneg k (2 * y)
  have b2 := tail_le_one hk (2 * y)
  have b3 := tail_le_one (k := k + 2) (by omega) (2 * y)
  linarith

theorem term_zero_le_one {y : ℝ} (hy : 0 ≤ y) : term 0 y ≤ 1 := by
  rw [term_zero_shape]
  exact exp_le_one_iff.mpr (by linarith)

/-! ### Monotonicity, continuity, and the quantile -/

theorem cdf_sub {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cdf k b - cdf k a = ∫ t in a..b, gammaPDFReal ((k : ℝ) / 2) (1 / 2) t := by
  have hs := shape_pos hk
  rw [cdf_eq_G, cdf_eq_G, G_eq_integral hs hb, G_eq_integral hs ha,
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_pdf hs 0 b)
      (intervalIntegrable_pdf hs 0 a)]

theorem cdf_strictMonoOn {k : ℕ} (hk : 1 ≤ k) : StrictMonoOn (cdf k) (Ici 0) := by
  intro a ha b hb hab
  have hs := shape_pos hk
  have h := cdf_sub hk ha hb
  have hp : 0 < ∫ t in a..b, gammaPDFReal ((k : ℝ) / 2) (1 / 2) t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_pdf hs a b)
      (fun t ht => gammaPDFReal_pos hs (by norm_num) (lt_of_le_of_lt ha ht.1)) hab
  linarith

theorem cdf_continuousOn {k : ℕ} (hk : 1 ≤ k) : ContinuousOn (cdf k) (Ici 0) := by
  have hs := shape_pos hk
  have hc : Continuous fun b => ∫ t in (0 : ℝ)..b, gammaPDFReal ((k : ℝ) / 2) (1 / 2) t :=
    intervalIntegral.continuous_primitive (intervalIntegrable_pdf hs) 0
  exact hc.continuousOn.congr fun x hx => G_eq_integral hs hx

/-- `[lo, hi]` holds the quantile of the chi-square distribution at `p`: `0 ≤ lo ≤ hi`, and
exactly one real `x` has `cdf k x = p`, which lies in `[lo, hi]`. -/
def QuantileIn (k : ℕ) (p lo hi : ℝ) : Prop :=
  0 ≤ lo ∧ lo ≤ hi ∧ ∃ x, lo ≤ x ∧ x ≤ hi ∧ cdf k x = p ∧ ∀ y, cdf k y = p → y = x

theorem quantileIn_of {k : ℕ} (hk : 1 ≤ k) {p a c : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hpa : cdf k a < p) (hpc : p ≤ cdf k c) : QuantileIn k p a c := by
  have hm := cdf_strictMonoOn hk
  have hac : a < c := by
    by_contra h
    have := hm.monotoneOn hc ha (not_lt.mp h)
    linarith
  obtain ⟨x, hx, hpx⟩ := intermediate_value_Icc hac.le
    ((cdf_continuousOn hk).mono fun t ht => le_trans ha ht.1) ⟨hpa.le, hpc⟩
  have hx0 : 0 ≤ x := ha.trans hx.1
  refine ⟨ha, hac.le, x, hx.1, hx.2, hpx, fun y hy => ?_⟩
  have hy0 : 0 ≤ y := by
    by_contra h
    rw [cdf_neg hk (not_le.mp h)] at hy
    linarith
  exact hm.injOn hy0 hx0 (hy.trans hpx.symm)

#print axioms G_succ
#print axioms G_one
#print axioms G_half
#print axioms tail_closed
#print axioms term_succ
#print axioms term_half
#print axioms term_le_one
#print axioms cdf_strictMonoOn
#print axioms cdf_continuousOn
#print axioms quantileIn_of

end Demos.Gate.Model
