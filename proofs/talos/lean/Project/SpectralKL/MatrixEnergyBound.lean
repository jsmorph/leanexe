import Project.SpectralKL.MatrixEstimator

namespace Project.SpectralKL.MatrixPolynomial
open Matrix Samples DensePolynomial MeasureTheory intervalIntegral
open scoped Matrix
variable {m : Nat}

/-- Any computed polynomial vector with a uniform squared-residual bound gives
an integral error bound. No approximate inverse or proposed score is assumed. -/
theorem energy_integral_error (p q : List (Fin m → ℚ)) (eta : ℚ) (he : 0 < eta)
    (x : Vector Poly m) (E : ℝ)
    (hres : ∀ r ∈ Set.Icc (0:ℝ) 1,
      MatrixIteration.normSq (mean (realRows p)-mean (realRows q)-
        Samples.system (realRows p) (realRows q) (eta:ℝ) r *ᵥ
          (fun i => eval (view x i) r)) ≤ E) :
    |(integrate (mul [1,-1] (energy (moment p) (moment q) (mean p-mean q) eta x)):ℝ)-
      Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤ E/(2*(eta:ℝ)) := by
  let d := mean (realRows p)-mean (realRows q)
  let poly := mul [1,-1] (energy (moment p) (moment q) (mean p-mean q) eta x)
  let g := eval poly
  have heR : (0:ℝ) < eta := by exact_mod_cast he
  have hg (r : ℝ) : g r = (1-r)*Residual.energy
      (Samples.system (realRows p) (realRows q) (eta:ℝ) r) d (fun i => eval (view x i) r) := by
    dsimp [g,poly]
    rw [eval_mul,energy_eval,moment_cast,moment_cast,difference_cast]
    simp [eval,Samples.system,d,sub_eq_add_neg]
  have hpoint (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) :
      g r ≤ Certificate.integrand (realRows p) (realRows q) (eta:ℝ) r ∧
      Certificate.integrand (realRows p) (realRows q) (eta:ℝ) r ≤ g r+(1-r)*(E/(eta:ℝ)) := by
    have bounds := Residual.quadratic_bounds
      (Samples.system (realRows p) (realRows q) (eta:ℝ) r)
      (system_symmetric (realRows p) (realRows q) (eta:ℝ) r) (eta:ℝ)
      heR (system_coercive (realRows p) (realRows q) (eta:ℝ) r hr) d
      (fun i => eval (view x i) r)
    have hu := div_le_div_of_nonneg_right (hres r hr) heR.le
    have hw : 0 ≤ 1-r := sub_nonneg.mpr hr.2
    rw [hg]
    constructor
    · exact mul_le_mul_of_nonneg_left bounds.1 hw
    · have h := mul_le_mul_of_nonneg_left (bounds.2.trans (add_le_add le_rfl hu)) hw
      simpa only [mul_add,Certificate.integrand,d] using h
  have hf := Certificate.integrand_integrable (realRows p) (realRows q) (eta:ℝ) heR
    (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 1)
  have hgi : IntervalIntegrable g volume 0 1 := (eval_continuous poly).intervalIntegrable (0:ℝ) 1
  have hci : IntervalIntegrable (fun r : ℝ => (1-r)*(E/(eta:ℝ))) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hl := integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hgi hf (fun r hr => (hpoint r hr).1)
  have hu := integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hf (hgi.add hci) (fun r hr => (hpoint r hr).2)
  have hscore : (∫ r in (0:ℝ)..1, g r) = (integrate poly:ℝ) := (integrate_correct poly).symm
  rw [hscore] at hl
  rw [intervalIntegral.integral_add hgi hci,hscore,Certificate.weighted_const_integral] at hu
  change (integrate poly:ℝ) ≤ Certificate.target _ _ _ at hl
  change Certificate.target _ _ _ ≤ (integrate poly:ℝ)+_ at hu
  change |(integrate poly:ℝ)-_| ≤ _
  rw [abs_of_nonpos (sub_nonpos.mpr hl)]
  norm_num at hu
  rw [show E/(2*(eta:ℝ)) = E/(eta:ℝ)*(1/2) by ring]
  linarith

end Project.SpectralKL.MatrixPolynomial
