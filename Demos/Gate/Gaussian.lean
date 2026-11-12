import Demos.Gate.Model
import Demos.Gate.Mahalanobis
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Complex.Convex

/-!
The law of the squared Mahalanobis distance under the Gaussian model.  For `d ≥ 1`, a positive
definite `d × d` matrix `S`, and an innovation `ν` distributed as Mathlib's
`multivariateGaussian 0 S`, `gaussian_chiSquare` states that `mahalanobis S ν` has the law
`chiSquare d`, and `gaussian_tail` that the probability that it exceeds `γ` is `tail d γ`.

`multivariateGaussian 0 S` is the image of the standard Gaussian under `√S = CFC.sqrt S`, and
`map_pi_eq_stdGaussian` gives the standard Gaussian as the image of the product of `d` standard
normal laws.  Since `√S S⁻¹ √S = 1`, the distance of `√S z` is `Σ z_i²` (`mahalanobis_sqrt`), so
the law of the distance is that of the sum of the squares of `d` independent standard normal
variables (`map_mahalanobis`).  For `t < 1/2`, the moment-generating function of that sum and
that of `chiSquare d` are both `(1/2 / (1/2 - t))^(d/2)`, and `ext_of_mgf_Iio` concludes that the
two laws are equal: their complex moment-generating functions are analytic on the half-plane
`re z < 1/2` and agree at its real points, so they agree on the imaginary axis, where they are the
characteristic functions.
-/

namespace Demos.Gate.Model

open Real MeasureTheory Set ProbabilityTheory Filter Topology WithLp
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

/-! ### Uniqueness from moment-generating functions on a half-line -/

/-- Two probability measures on `ℝ` whose moment-generating functions are finite and equal on
`(-∞, c)`, with `c > 0`, are equal. -/
theorem ext_of_mgf_Iio {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c : ℝ} (hc : 0 < c) (hμ : ∀ t < c, Integrable (fun x => exp (t * x)) μ)
    (hν : ∀ t < c, Integrable (fun x => exp (t * x)) ν)
    (h : ∀ t < c, ∫ x, exp (t * x) ∂μ = ∫ x, exp (t * x) ∂ν) : μ = ν := by
  have hsub : ∀ ρ : Measure ℝ, (∀ t < c, Integrable (fun x => exp (t * x)) ρ) →
      {z : ℂ | z.re < c} ⊆ {z | z.re ∈ interior (integrableExpSet id ρ)} := fun ρ hρ _ hz =>
    interior_maximal (s := integrableExpSet id ρ) (fun t ht => hρ t ht) isOpen_Iio hz
  have hf := (analyticOnNhd_complexMGF (X := id) (μ := μ)).mono (hsub μ hμ)
  have hg := (analyticOnNhd_complexMGF (X := id) (μ := ν)).mono (hsub ν hν)
  have hpts : Tendsto (fun n : ℕ => ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
      rw [neg_zero] at h1
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      rwa [Complex.ofReal_zero] at h2
    · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero, neg_eq_zero]
      exact this.ne'
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), complexMGF id μ z = complexMGF id ν z := by
    refine hpts.frequently (Frequently.of_forall fun n => ?_)
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [complexMGF_ofReal, complexMGF_ofReal]
    exact congrArg _ (h _ (by linarith))
  have heq := hf.eqOn_of_preconnected_of_frequently_eq hg
    (convex_halfSpace_re_lt c).isPreconnected (by simpa using hc) hfreq
  refine Measure.ext_of_charFun (funext fun s => ?_)
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact heq (by simpa using hc)

/-! ### Moment-generating functions -/

theorem integral_exp_mul_gamma {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    ∫ x, exp (t * x) ∂(gammaMeasure a r) = (r / (r - t)) ^ a := by
  have hrt : 0 < r - t := by linarith
  have hpt : ∀ x, (gammaPDF a r x).toReal • exp (t * x) = (Ici 0).indicator
      (fun x => r ^ a / Gamma a * (x ^ (a - 1) * exp (-((r - t) * x)))) x := by
    intro x
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x), smul_eq_mul, gammaPDFReal]
    by_cases hx : 0 ≤ x
    · rw [ite_eq_left hx, indicator_of_mem (mem_Ici.mpr hx),
        show -((r - t) * x) = -(r * x) + t * x by ring, exp_add]
      ring
    · rw [ite_eq_right hx, indicator_of_notMem (by simpa using hx), zero_mul]
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul (f := gammaPDF a r)
    (measurable_gammaPDFReal a r).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_Ioi ha hrt, div_eq_mul_one_div r (r - t),
    mul_rpow hr.le (by positivity), mul_comm ((1 / (r - t)) ^ a) (Gamma a), ← mul_assoc,
    div_mul_cancel₀ _ (Gamma_pos_of_pos ha).ne']

/-- The moment-generating function of the chi-square distribution below `1/2`. -/
theorem integral_exp_mul_chiSquare {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : t < 1 / 2) :
    ∫ x, exp (t * x) ∂(chiSquare k) = (1 / 2 / (1 / 2 - t)) ^ ((k : ℝ) / 2) :=
  integral_exp_mul_gamma (shape_pos hk) (by norm_num) ht

/-- The moment-generating function of the square of a standard normal variable below `1/2`. -/
theorem integral_exp_mul_sq {t : ℝ} (ht : t < 1 / 2) :
    ∫ x, exp (t * x ^ 2) ∂(gaussianReal 0 1) = (1 / 2 / (1 / 2 - t)) ^ (1 / 2 : ℝ) := by
  have hb : 0 < 1 / 2 - t := by linarith
  have hpi := pi_pos
  have hpt : ∀ x : ℝ, gaussianPDFReal 0 1 x • exp (t * x ^ 2) =
      (√(2 * π))⁻¹ * exp (-(1 / 2 - t) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [mul_assoc, ← exp_add, show -x ^ 2 / 2 + t * x ^ 2 = -(1 / 2 - t) * x ^ 2 by ring]
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp_rw [hpt]
  rw [integral_const_mul, integral_gaussian, ← sqrt_inv, ← sqrt_mul (by positivity), sqrt_eq_rpow]
  congr 1
  field_simp

/-- The product of `d` standard normal laws. -/
noncomputable abbrev stdNormal (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- The sum of the squares of the coordinates. -/
def sumSq {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2

theorem measurable_sumSq (d : ℕ) : Measurable (sumSq (d := d)) :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2

theorem integral_exp_mul_sumSq {d : ℕ} {t : ℝ} (ht : t < 1 / 2) :
    ∫ x, exp (t * x) ∂((stdNormal d).map sumSq) =
      ((1 / 2 / (1 / 2 - t)) ^ (1 / 2 : ℝ)) ^ d := by
  rw [integral_map (measurable_sumSq d).aemeasurable
    (by fun_prop : Continuous fun x : ℝ => exp (t * x)).aestronglyMeasurable]
  have hpt : ∀ x : Fin d → ℝ, exp (t * sumSq x) = ∏ i, exp (t * x i ^ 2) := by
    intro x
    rw [sumSq, Finset.mul_sum, exp_sum]
  simp_rw [hpt]
  rw [integral_fintype_prod_eq_prod (fun _ y => exp (t * y ^ 2))]
  simp [integral_exp_mul_sq ht]

/-- The sum of the squares of `d` independent standard normal variables has the chi-square
distribution with `d` degrees of freedom. -/
theorem map_sumSq {d : ℕ} (hd : 1 ≤ d) : (stdNormal d).map sumSq = chiSquare d := by
  have := isProbability_of hd
  have : IsProbabilityMeasure ((stdNormal d).map sumSq) :=
    Measure.isProbabilityMeasure_map (measurable_sumSq d).aemeasurable
  have hb : ∀ t < (1 / 2 : ℝ), 0 < 1 / 2 / (1 / 2 - t) := fun t ht =>
    div_pos (by norm_num) (by linarith)
  have hval : ∀ t < (1 / 2 : ℝ), ∫ x, exp (t * x) ∂((stdNormal d).map sumSq) =
      (1 / 2 / (1 / 2 - t)) ^ ((d : ℝ) / 2) := by
    intro t ht
    rw [integral_exp_mul_sumSq ht, ← rpow_natCast, ← rpow_mul (hb t ht).le]
    congr 1
    ring
  refine ext_of_mgf_Iio (by norm_num : (0 : ℝ) < 1 / 2) (fun t ht => ?_) (fun t ht => ?_)
    fun t ht => ?_
  · refine Integrable.of_integral_ne_zero ?_
    rw [hval t ht]
    exact (rpow_pos_of_pos (hb t ht) _).ne'
  · refine Integrable.of_integral_ne_zero ?_
    rw [integral_exp_mul_chiSquare hd ht]
    exact (rpow_pos_of_pos (hb t ht) _).ne'
  · rw [hval t ht, integral_exp_mul_chiSquare hd ht]

/-! ### Whitening -/

/-- The squared Mahalanobis distance of `√S x` is the sum of the squares of `x`. -/
theorem mahalanobis_sqrt {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (x : Fin d → ℝ) : mahalanobis S (CFC.sqrt S *ᵥ x) = sumSq x := by
  set A := CFC.sqrt S
  have hAA : A * A = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hAt : A.transpose = A := by
    have h := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hdet : IsUnit A.det := by
    have h := hS.det_pos.ne'
    rw [← hAA, Matrix.det_mul] at h
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul h)
  have hinv : A * (S⁻¹ * A) = 1 := by
    rw [← hAA, Matrix.mul_inv_rev, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv A hdet,
      one_mul, Matrix.nonsing_inv_mul A hdet]
  unfold mahalanobis
  rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose A x, hAt, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  simp [dotProduct, sumSq, sq]

theorem measurable_mahalanobis {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    Measurable fun ν : EuclideanSpace ℝ (Fin d) => mahalanobis S (ofLp ν) := by
  refine Continuous.measurable ?_
  simp only [mahalanobis, dotProduct, Matrix.mulVec]
  fun_prop

/-- The law of the squared Mahalanobis distance under `multivariateGaussian 0 S` is the law of the
sum of the squares of `d` independent standard normal variables. -/
theorem map_mahalanobis {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    (multivariateGaussian 0 S).map (fun ν => mahalanobis S (ofLp ν)) =
      (stdNormal d).map sumSq := by
  have hF : Measurable fun z : EuclideanSpace ℝ (Fin d) =>
      (0 : EuclideanSpace ℝ (Fin d)) + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) z := by
    fun_prop
  rw [multivariateGaussian, ← map_pi_eq_stdGaussian, Measure.map_map (measurable_mahalanobis S) hF,
    Measure.map_map ((measurable_mahalanobis S).comp hF) (by fun_prop)]
  congr 1
  funext x
  simp [mahalanobis_sqrt hS]

/-! ### The law of the distance -/

/-- For `d ≥ 1` and a positive definite `S`, the squared Mahalanobis distance of an innovation
distributed as `multivariateGaussian 0 S` has the chi-square distribution with `d` degrees of
freedom. -/
theorem gaussian_chiSquare {d : ℕ} (hd : 1 ≤ d) {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosDef) :
    (multivariateGaussian 0 S).map (fun ν => mahalanobis S (ofLp ν)) = chiSquare d := by
  rw [map_mahalanobis hS, map_sumSq hd]

/-- For `d ≥ 1`, a positive definite `S`, and every `γ`, the probability that the squared
Mahalanobis distance of an innovation distributed as `multivariateGaussian 0 S` exceeds `γ` is
`tail d γ`. -/
theorem gaussian_tail {d : ℕ} (hd : 1 ≤ d) {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (γ : ℝ) : (multivariateGaussian 0 S).real {ν | γ < mahalanobis S (ofLp ν)} = tail d γ := by
  rw [tail, ← gaussian_chiSquare hd hS,
    map_measureReal_apply (measurable_mahalanobis S) measurableSet_Ioi]
  rfl

#print axioms ext_of_mgf_Iio
#print axioms map_sumSq
#print axioms map_mahalanobis
#print axioms gaussian_chiSquare
#print axioms gaussian_tail

end Demos.Gate.Model
