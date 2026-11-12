import Demos.Conjunction.Model
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Function.Jacobian

/-!
This file relates the probability of collision `Model.pc` to Mathlib's multivariate Gaussian
distribution.  For a covariance with `0 < c11` and `0 < c11 * c22 - c12 ^ 2`,
`multivariateGaussian_eq_withDensity` states that `multivariateGaussian` with mean `(m1, m2)` and
covariance matrix `!![c11, c12; c12, c22]` equals Lebesgue measure on `EuclideanSpace ℝ (Fin 2)`
with the density `Model.density`.  `pc_eq_multivariateGaussian` states that `Model.pc` with radius
`r` equals the measure under that distribution, as a real number, of the set where
`x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2`, the disk that `Model.disk` defines.  The corollaries
`integral_density` and `pc_le_one` state that the density integrates to 1 over the plane and that
`Model.pc` is at most 1.

Mathlib defines `multivariateGaussian μ S` as the image of the standard Gaussian under
`x ↦ μ + A x`, where `A` is the square root of `S` from the continuous functional calculus.
`map_stdGaussian_eq_withDensity` computes the density of that image for every matrix `A` with
`A * Aᵀ` equal to the covariance, by the change of variables
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`, so the proof uses only the symmetry of the
square root and the identity `A * A = S`.  The standard Gaussian on `EuclideanSpace ℝ (Fin 2)` is
the image under `toLp` of the product of two copies of `gaussianReal 0 1`, and
`pi_gaussianReal_eq_withDensity` gives that product its density on `Fin 2 → ℝ`.
-/

namespace Demos.Conjunction.Gaussian

open MeasureTheory ProbabilityTheory Real WithLp Set
open Demos.Conjunction.Model
open scoped Matrix MatrixOrder

theorem density_nonneg (m1 m2 c11 c12 c22 : ℝ) (p : ℝ × ℝ) :
    0 ≤ density m1 m2 c11 c12 c22 p := by
  unfold density
  positivity

/-- When the covariance is `A * Aᵀ` with `A = !![a, b; c, d]`, the density at the image of `z`
under `z ↦ m + A z`, times `|det A|`, is the standard Gaussian density at `z`. -/
theorem abs_det_mul_density (m1 m2 a b c d z0 z1 : ℝ) (hδ : a * d - b * c ≠ 0) :
    |a * d - b * c| *
        density m1 m2 (a * a + b * b) (a * c + b * d) (c * c + d * d)
          (m1 + (a * z0 + b * z1), m2 + (c * z0 + d * z1)) =
      gaussianPDFReal 0 1 z0 * gaussianPDFReal 0 1 z1 := by
  have hdet : det (a * a + b * b) (a * c + b * d) (c * c + d * d) = (a * d - b * c) ^ 2 := by
    unfold det
    ring
  have hq : (c * c + d * d) * (m1 + (a * z0 + b * z1) - m1) ^ 2 -
        2 * (a * c + b * d) * (m1 + (a * z0 + b * z1) - m1) * (m2 + (c * z0 + d * z1) - m2) +
        (a * a + b * b) * (m2 + (c * z0 + d * z1) - m2) ^ 2 =
      (a * d - b * c) ^ 2 * (z0 ^ 2 + z1 ^ 2) := by
    ring
  have he : -((a * d - b * c) ^ 2 * (z0 ^ 2 + z1 ^ 2)) / (2 * (a * d - b * c) ^ 2) =
      -z0 ^ 2 / 2 + -z1 ^ 2 / 2 := by
    field_simp
    ring
  have hc : |a * d - b * c| * (2 * π * |a * d - b * c|)⁻¹ = (√(2 * π))⁻¹ * (√(2 * π))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    field_simp
  unfold density gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [hdet, hq, Real.sqrt_sq_eq_abs, he, Real.exp_add, ← mul_assoc, hc]
  ring

/-- The product of two standard Gaussians on `Fin 2 → ℝ` has the product density. -/
theorem pi_gaussianReal_eq_withDensity :
    Measure.pi (fun _ : Fin 2 => gaussianReal 0 1) =
      volume.withDensity fun z : Fin 2 → ℝ => gaussianPDF 0 1 (z 0) * gaussianPDF 0 1 (z 1) := by
  refine Measure.pi_eq fun s hs => ?_
  have hpre : univ.pi s = MeasurableEquiv.finTwoArrow ⁻¹' (s 0 ×ˢ s 1) := by
    ext z
    simp [Fin.forall_fin_two]
  have hG : ∀ t, MeasurableSet t → gaussianReal 0 1 t = ∫⁻ x in t, gaussianPDF 0 1 x := by
    intro t ht
    rw [gaussianReal_of_var_ne_zero _ one_ne_zero, withDensity_apply _ ht]
  have h := (volume_preserving_finTwoArrow ℝ).setLIntegral_comp_preimage ((hs 0).prod (hs 1))
    (f := fun p : ℝ × ℝ => gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2)
    ((measurable_gaussianPDF 0 1).comp measurable_fst |>.mul
      ((measurable_gaussianPDF 0 1).comp measurable_snd))
  rw [← hpre] at h
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  refine h.trans ?_
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (measurable_gaussianPDF 0 1).aemeasurable
      (measurable_gaussianPDF 0 1).aemeasurable,
    Fin.prod_univ_two, hG _ (hs 0), hG _ (hs 1)]

/-- The image of the standard Gaussian on `EuclideanSpace ℝ (Fin 2)` under `x ↦ m + A x`, for
any matrix `A` with `A * Aᵀ` equal to a positive definite covariance, has the density
`Model.density`. -/
theorem map_stdGaussian_eq_withDensity (m1 m2 c11 c12 c22 : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A * A.transpose = !![c11, c12; c12, c22]) (hd : 0 < det c11 c12 c22) :
    (stdGaussian (EuclideanSpace ℝ (Fin 2))).map
        (fun x => !₂[m1, m2] + Matrix.toEuclideanCLM (𝕜 := ℝ) A x) =
      volume.withDensity fun x : EuclideanSpace ℝ (Fin 2) =>
        ENNReal.ofReal (density m1 m2 c11 c12 c22 (x 0, x 1)) := by
  have entry : ∀ i j, (A * A.transpose) i j = A i 0 * A j 0 + A i 1 * A j 1 := by
    intro i j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : A 0 0 * A 0 0 + A 0 1 * A 0 1 = c11 := by
    rw [← entry, hA]
    rfl
  have h12 : A 0 0 * A 1 0 + A 0 1 * A 1 1 = c12 := by
    rw [← entry, hA]
    rfl
  have h22 : A 1 0 * A 1 0 + A 1 1 * A 1 1 = c22 := by
    rw [← entry, hA]
    rfl
  have hδ : A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0 := by
    intro h0
    have h : det c11 c12 c22 = (A 0 0 * A 1 1 - A 0 1 * A 1 0) ^ 2 := by
      rw [← h11, ← h12, ← h22]
      unfold det
      ring
    rw [h, h0] at hd
    simp at hd
  have hunit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two, isUnit_iff_ne_zero]
    exact hδ
  let L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' A)
  have hL : ∀ z, L z = A *ᵥ z := fun z => rfl
  have hdet : L.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
    rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin',
      Matrix.det_fin_two]
  let F : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun z => ![m1, m2] + L z
  have hFmeas : Measurable F := (continuous_const.add L.continuous).measurable
  have hinj : Function.Injective F := fun z w h =>
    Matrix.mulVec_injective_iff_isUnit.2 hunit (add_left_cancel h)
  have hsurj : Function.Surjective F := by
    intro w
    obtain ⟨z, hz⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hunit (w - ![m1, m2])
    refine ⟨z, ?_⟩
    show ![m1, m2] + L z = w
    rw [hL, hz]
    abel
  have hkE : Measurable fun x : EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (density m1 m2 c11 c12 c22 (x 0, x 1)) :=
    ((continuous_density m1 m2 c11 c12 c22).comp (by fun_prop)).measurable.ennreal_ofReal
  have hT : Measurable fun x : EuclideanSpace ℝ (Fin 2) =>
      !₂[m1, m2] + Matrix.toEuclideanCLM (𝕜 := ℝ) A x := by
    fun_prop
  have htoLp := PiLp.volume_preserving_toLp (Fin 2)
  ext s hs
  have hs' : MeasurableSet (toLp 2 ⁻¹' s : Set (Fin 2 → ℝ)) := htoLp.measurable hs
  have hpre : (fun x : EuclideanSpace ℝ (Fin 2) =>
      !₂[m1, m2] + Matrix.toEuclideanCLM (𝕜 := ℝ) A x) ∘ toLp 2 ⁻¹' s =
        F ⁻¹' (toLp 2 ⁻¹' s) :=
    rfl
  rw [← map_pi_eq_stdGaussian, Measure.map_map hT htoLp.measurable,
    Measure.map_apply (hT.comp htoLp.measurable) hs, hpre, pi_gaussianReal_eq_withDensity,
    withDensity_apply _ (hFmeas hs'), withDensity_apply _ hs,
    ← htoLp.setLIntegral_comp_preimage hs hkE]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hFmeas hs')
    (fun z _ => ((L.hasFDerivAt (x := z)).const_add ![m1, m2]).hasFDerivWithinAt) hinj.injOn
    (fun y => ENNReal.ofReal (density m1 m2 c11 c12 c22 (y 0, y 1)))
  rw [image_preimage_eq _ hsurj] at hcv
  refine Eq.trans ?_ hcv.symm
  refine setLIntegral_congr_fun (hFmeas hs') fun z _ => ?_
  have hF0 : (![m1, m2] + L z) 0 = m1 + (A 0 0 * z 0 + A 0 1 * z 1) := by
    show m1 + (fun j => A 0 j) ⬝ᵥ z = _
    rw [Matrix.vec2_dotProduct]
  have hF1 : (![m1, m2] + L z) 1 = m2 + (A 1 0 * z 0 + A 1 1 * z 1) := by
    show m2 + (fun j => A 1 j) ⬝ᵥ z = _
    rw [Matrix.vec2_dotProduct]
  rw [hF0, hF1, hdet, ← ENNReal.ofReal_mul (abs_nonneg _), ← h11, ← h12, ← h22,
    abs_det_mul_density _ _ _ _ _ _ _ _ hδ, ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  rfl

/-- The covariance matrix is positive semidefinite. -/
theorem posSemidef_cov {c11 c12 c22 : ℝ} (hc : 0 < c11) (hd : 0 < det c11 c12 c22) :
    (!![c11, c12; c12, c22] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    unfold det at hd
    nlinarith [sq_nonneg (c11 * x 0 + c12 * x 1), mul_nonneg hd.le (sq_nonneg (x 1))]

/-- Mathlib's multivariate Gaussian with mean `(m1, m2)` and covariance
`!![c11, c12; c12, c22]` is Lebesgue measure with the density `Model.density`. -/
theorem multivariateGaussian_eq_withDensity (m1 m2 c11 c12 c22 : ℝ) (hc : 0 < c11)
    (hd : 0 < det c11 c12 c22) :
    multivariateGaussian !₂[m1, m2] !![c11, c12; c12, c22] =
      volume.withDensity fun x : EuclideanSpace ℝ (Fin 2) =>
        ENNReal.ofReal (density m1 m2 c11 c12 c22 (x 0, x 1)) := by
  have hS := posSemidef_cov hc hd
  have hsa : IsSelfAdjoint (CFC.sqrt (!![c11, c12; c12, c22] : Matrix (Fin 2) (Fin 2) ℝ)) :=
    (CFC.sqrt_nonneg _).isSelfAdjoint
  have hmul := CFC.sqrt_mul_sqrt_self _ hS.nonneg
  rw [multivariateGaussian]
  refine map_stdGaussian_eq_withDensity m1 m2 c11 c12 c22 _ ?_ hd
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose, hsa.star_eq,
    hmul]

/-- The coordinates `(x 0, x 1)` carry Lebesgue measure on `EuclideanSpace ℝ (Fin 2)` to
Lebesgue measure on `ℝ × ℝ`. -/
theorem volume_preserving_coords :
    MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 2) => (x 0, x 1)) :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

/-- `Model.pc` is the measure under Mathlib's multivariate Gaussian of the disk of radius `r`
about the origin. -/
theorem pc_eq_multivariateGaussian (m1 m2 c11 c12 c22 r : ℝ) (hc : 0 < c11)
    (hd : 0 < det c11 c12 c22) :
    pc m1 m2 c11 c12 c22 r =
      (multivariateGaussian !₂[m1, m2] !![c11, c12; c12, c22]).real
        {x | x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2} := by
  have hdisk : MeasurableSet (disk r) :=
    (isClosed_le (f := fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (g := fun _ => r ^ 2) (by fun_prop)
      continuous_const).measurableSet
  have hf : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (density m1 m2 c11 c12 c22 p) :=
    (continuous_density m1 m2 c11 c12 c22).measurable.ennreal_ofReal
  have h := volume_preserving_coords.setLIntegral_comp_preimage hdisk hf
  rw [measureReal_def, multivariateGaussian_eq_withDensity m1 m2 c11 c12 c22 hc hd,
    show {x : EuclideanSpace ℝ (Fin 2) | x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2} =
      (fun x : EuclideanSpace ℝ (Fin 2) => (x 0, x 1)) ⁻¹' disk r from rfl,
    withDensity_apply _ (volume_preserving_coords.measurable hdisk), h, pc,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (density_nonneg m1 m2 c11 c12 c22))
      (continuous_density m1 m2 c11 c12 c22).aestronglyMeasurable]

/-- The density integrates to 1 over the plane. -/
theorem integral_density (m1 m2 c11 c12 c22 : ℝ) (hc : 0 < c11) (hd : 0 < det c11 c12 c22) :
    ∫ p, density m1 m2 c11 c12 c22 p = 1 := by
  have hf : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (density m1 m2 c11 c12 c22 p) :=
    (continuous_density m1 m2 c11 c12 c22).measurable.ennreal_ofReal
  have h1 := measure_univ (μ := multivariateGaussian !₂[m1, m2] !![c11, c12; c12, c22])
  rw [multivariateGaussian_eq_withDensity m1 m2 c11 c12 c22 hc hd,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  have h2 := volume_preserving_coords.lintegral_comp hf
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (density_nonneg m1 m2 c11 c12 c22))
      (continuous_density m1 m2 c11 c12 c22).aestronglyMeasurable, ← h2, h1, ENNReal.toReal_one]

/-- `Model.pc` is at most 1. -/
theorem pc_le_one (m1 m2 c11 c12 c22 r : ℝ) (hc : 0 < c11) (hd : 0 < det c11 c12 c22) :
    pc m1 m2 c11 c12 c22 r ≤ 1 := by
  rw [pc_eq_multivariateGaussian m1 m2 c11 c12 c22 r hc hd]
  exact measureReal_le_one

#print axioms map_stdGaussian_eq_withDensity
#print axioms multivariateGaussian_eq_withDensity
#print axioms pc_eq_multivariateGaussian
#print axioms integral_density
#print axioms pc_le_one

end Demos.Conjunction.Gaussian

