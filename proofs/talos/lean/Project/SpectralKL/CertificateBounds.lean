import Project.SpectralKL.CertificateData

namespace Project.SpectralKL.Certificate
open Matrix Samples Residual MeasureTheory Set intervalIntegral
open scoped Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem integrand_continuousOn (p q : List (n → ℝ)) (eta : ℝ) (he : 0 < eta) :
    ContinuousOn (integrand p q eta) (Icc 0 1) := by
  have hc : Continuous (system p q eta) := by unfold system; fun_prop
  have hi : ContinuousOn (fun r => (system p q eta r)⁻¹) (Icc 0 1) := by
    intro r hr
    have hp := Residual.posDef _ (system_symmetric p q eta r) eta he
      (system_coercive p q eta r hr)
    have hd : (system p q eta r).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit).ne_zero
    have hv := continuousAt_matrix_inv (system p q eta r)
      (by simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hd))
    exact (hv.comp hc.continuousAt).continuousWithinAt
  unfold integrand Residual.quadratic
  simp only [dotProduct, Matrix.mulVec]
  apply ContinuousOn.mul (by fun_prop)
  apply continuousOn_finset_sum
  intro i _
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finset_sum
  intro j _
  exact (continuousOn_pi.mp (continuousOn_pi.mp hi i) j).mul continuousOn_const

theorem integrand_integrable (p q : List (n → ℝ)) (eta : ℝ) (he : 0 < eta)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (integrand p q eta) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact (integrand_continuousOn p q eta he).mono (Icc_subset_Icc ha hb)

theorem energy_affine (p q : List (n → ℝ)) (eta r : ℝ) (x : n → ℝ) :
    energy (system p q eta r) (mean p-mean q) x =
      (2*((mean p-mean q) ⬝ᵥ x)-x ⬝ᵥ (action q x+eta•x)) +
        (x ⬝ᵥ (action q x-action p x))*r := by
  simp only [energy, system_action, systemAction, dotProduct_add, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  ring

theorem residual_affine (p q : List (n → ℝ)) (eta a b t : ℝ) (x : n → ℝ) :
    (mean p-mean q)-systemAction p q eta ((1-t)*a+t*b) x =
      (1-t) • ((mean p-mean q)-systemAction p q eta a x) +
        t • ((mean p-mean q)-systemAction p q eta b x) := by
  ext i
  simp only [systemAction, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem convex_square (a b t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ((1-t)*a+t*b)^2 ≤ a^2+b^2 := by
  have h := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg (a-b))
  nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg ht.1 (sq_nonneg a),
    mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg b)]

theorem residual_cell (p q : List (n → ℝ)) (eta a b r : ℝ) (x : n → ℝ)
    (hab : a < b) (hr : r ∈ Icc a b) :
    let d := mean p-mean q
    let er := d-systemAction p q eta r x
    let ea := d-systemAction p q eta a x
    let eb := d-systemAction p q eta b x
    er ⬝ᵥ er ≤ ea ⬝ᵥ ea + eb ⬝ᵥ eb := by
  dsimp only
  let t := (r-a)/(b-a)
  have ht : t ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hab.le)
    · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hr.2])
  have he : r = (1-t)*a+t*b := by
    dsimp [t]
    field_simp [(sub_pos.mpr hab).ne']
    <;> ring
  rw [he, residual_affine]
  simp only [dotProduct, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_two] using
    convex_square (((mean p-mean q)-systemAction p q eta a x) i)
      (((mean p-mean q)-systemAction p q eta b x) i) t ht

theorem weighted_affine_integral (a b u v : ℝ) :
    (∫ r in a..b, (1-r)*(u+v*r)) =
      u*((b-a)-(b^2-a^2)/2)+v*((b^2-a^2)/2-(b^3-a^3)/3) := by
  have he : (fun r : ℝ => (1-r)*(u+v*r)) =
      (fun r => u*(1-r)+v*(r-r^2)) := by ext r; ring
  rw [he, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun r : ℝ => u*(1-r))).intervalIntegrable a b)
    ((by fun_prop : Continuous (fun r : ℝ => v*(r-r^2))).intervalIntegrable a b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_id,
    intervalIntegral.integral_sub intervalIntegrable_id (intervalIntegrable_pow 2)]
  simp only [intervalIntegral.integral_const, integral_id, integral_pow, smul_eq_mul]
  norm_num

theorem weighted_const_integral (a b c : ℝ) :
    (∫ r in a..b, (1-r)*c) = c*((b-a)-(b^2-a^2)/2) := by
  simpa using weighted_affine_integral a b c 0

/-- A cell bounds the exact inverse quadratic integral over the whole interval,
including variation between the candidate's evaluation nodes. -/
theorem cell_sound (p q : List (n → ℝ)) (eta a b : ℝ) (x : n → ℝ)
    (he : 0 < eta) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (cell p q eta a b x).lower ≤ (∫ r in a..b, integrand p q eta r) ∧
      (∫ r in a..b, integrand p q eta r) ≤ (cell p q eta a b x).upper := by
  obtain rfl | hab' := hab.eq_or_lt
  · simp [cell]
  let d := mean p-mean q
  let g := fun r => energy (system p q eta r) d x
  let ea := d-systemAction p q eta a x
  let eb := d-systemAction p q eta b x
  let e := (ea ⬝ᵥ ea+eb ⬝ᵥ eb)/eta
  have hpoint (r : ℝ) (hr : r ∈ Icc a b) :
      (1-r)*g r ≤ integrand p q eta r ∧
        integrand p q eta r ≤ (1-r)*g r+(1-r)*e := by
    have hr01 : r ∈ Icc (0:ℝ) 1 := ⟨ha.trans hr.1,hr.2.trans hb⟩
    have h := quadratic_bounds (system p q eta r) (system_symmetric p q eta r)
      eta he (system_coercive p q eta r hr01) d x
    have hs := residual_cell p q eta a b r x hab' hr
    have hu := div_le_div_of_nonneg_right hs he.le
    rw [system_action] at h
    have hw : 0 ≤ 1-r := sub_nonneg.mpr hr01.2
    constructor
    · exact mul_le_mul_of_nonneg_left h.1 hw
    · have hh := mul_le_mul_of_nonneg_left (h.2.trans (add_le_add le_rfl hu)) hw
      rw [mul_add] at hh
      exact hh
  have hf := integrand_integrable p q eta he ha hab hb
  have hg : IntervalIntegrable (fun r => (1-r)*g r) volume a b := by
    dsimp [g,d]
    simp_rw [energy_affine]
    exact (by fun_prop : Continuous _).intervalIntegrable a b
  have hc : IntervalIntegrable (fun r : ℝ => (1-r)*e) volume a b :=
    (by fun_prop : Continuous _).intervalIntegrable a b
  have hl := integral_mono_on hab hg hf (fun r hr => (hpoint r hr).1)
  have hu := integral_mono_on hab hf (hg.add hc) (fun r hr => (hpoint r hr).2)
  have hgval : (∫ r in a..b, (1-r)*g r) = (cell p q eta a b x).lower := by
    dsimp [g,d]
    simp_rw [energy_affine]
    rw [weighted_affine_integral]
    rfl
  rw [hgval] at hl
  rw [integral_add hg hc, hgval, weighted_const_integral] at hu
  exact ⟨hl,hu⟩

#print axioms cell_sound
end Project.SpectralKL.Certificate
