import Project.Gelu.Perturbation
import Project.Gelu.Tail

namespace Project.Gelu.Real

noncomputable def argumentSlope (x : ℝ) : ℝ := 2*scale*(1+3*coefficient*x^2)
noncomputable def sigmoidSlope (x : ℝ) : ℝ := Real.exp (-x)/(1+Real.exp (-x))^2
noncomputable def correction (x : ℝ) : ℝ := x*sigmoidSlope (argument x)*argumentSlope x

theorem argument_derivative (x : ℝ) : HasDerivAt argument (argumentSlope x) x := by
  have h := ((hasDerivAt_id x).add (((hasDerivAt_id x).pow 3).const_mul coefficient)).const_mul
    (2*scale)
  change HasDerivAt (fun t : ℝ => 2*scale*(t+coefficient*t^3)) _ x
  convert h using 1 <;> first | rfl | (dsimp [argumentSlope]; ring)

theorem sigmoidSlope_nonnegative (x : ℝ) : 0 ≤ sigmoidSlope x := by
  unfold sigmoidSlope
  positivity

theorem sigmoidSlope_neg (x : ℝ) : sigmoidSlope (-x) = sigmoidSlope x := by
  have hp : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)
  have h1 : 1+Real.exp x ≠ 0 := by positivity
  have h2 : 1+(Real.exp x)⁻¹ ≠ 0 := by positivity
  unfold sigmoidSlope
  rw [neg_neg, Real.exp_neg]
  field_simp
  ring

theorem sigmoidSlope_le_exp (x : ℝ) : sigmoidSlope x ≤ Real.exp (-x) := by
  unfold sigmoidSlope
  apply (div_le_iff₀ (by positivity)).mpr
  have h : 1 ≤ (1+Real.exp (-x))^2 := by nlinarith [Real.exp_pos (-x)]
  nlinarith [mul_le_mul_of_nonneg_left h (Real.exp_pos (-x)).le]

theorem correction_bounds (x : ℝ) (hx : 0 ≤ x) : 0 ≤ correction x ∧ correction x ≤ 3 := by
  have hk : 0 ≤ scale := Real.sqrt_nonneg _
  have hc : 0 ≤ coefficient := by norm_num [coefficient]
  have harg := argument_nonnegative x hx
  have hs := sigmoidSlope_nonnegative (argument x)
  have hder : 0 ≤ argumentSlope x := by unfold argumentSlope; positivity
  have hpoly : x*argumentSlope x ≤ 3*argument x := by
    unfold argumentSlope argument
    nlinarith [mul_nonneg hx hk]
  have hexp : argument x*Real.exp (-argument x) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith [Real.add_one_le_exp (argument x)]
  have hslope : argument x*sigmoidSlope (argument x) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (sigmoidSlope_le_exp _) harg).trans hexp
  constructor
  · exact mul_nonneg (mul_nonneg hx hs) hder
  · have h := mul_le_mul_of_nonneg_right hpoly hs
    unfold correction
    nlinarith only [h, hslope]

theorem correction_neg (x : ℝ) : correction (-x) = -correction x := by
  simp only [correction, argument_neg, sigmoidSlope_neg, argumentSlope, neg_sq]
  ring

theorem correction_magnitude (x : ℝ) : |correction x| ≤ 3 := by
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg (correction_bounds x h).1]
    exact (correction_bounds x h).2
  · have hh := correction_bounds (-x) (by linarith)
    have he : |correction (-x)| ≤ 3 := by rw [abs_of_nonneg hh.1]; exact hh.2
    simpa only [correction_neg, abs_neg] using he

theorem gelu_derivative (x : ℝ) :
    HasDerivAt gelu (sigmoid (argument x)+correction x) x := by
  have h := (hasDerivAt_id x).mul ((sigmoid_derivative (argument x)).comp x (argument_derivative x))
  have hfun : gelu = fun t => t*sigmoid (argument t) := by
    funext t
    rw [gelu_logistic, sigmoid]
    ring
  rw [hfun]
  convert h using 1 <;> first | rfl | (dsimp [sigmoidSlope, correction]; ring)

theorem gelu_derivative_bound (x : ℝ) : |sigmoid (argument x)+correction x| ≤ 4 := by
  have hs : |sigmoid (argument x)| ≤ 1 := by
    rw [abs_of_nonneg (sigmoid_bounds _).1]
    exact (sigmoid_bounds _).2
  exact (abs_add_le _ _).trans (by linarith [correction_magnitude x])

theorem gelu_lipschitz_global (x y : ℝ) : |gelu x-gelu y| ≤ 4*|x-y| := by
  have ordered (a b : ℝ) (hab : a ≤ b) : |gelu b-gelu a| ≤ 4*(b-a) := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t (_ : t ∈ Set.Icc a b) => (gelu_derivative t).hasDerivWithinAt)
      (fun t (_ : t ∈ Set.Ico a b) => by
        simpa only [Real.norm_eq_abs] using gelu_derivative_bound t)
      b ⟨hab, le_refl _⟩
    simpa only [Real.norm_eq_abs] using h
  rcases le_total x y with h | h
  · rw [abs_sub_comm, abs_of_nonpos (by linarith : x-y ≤ 0)]
    have hh := ordered x y h
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact ordered y x h

#print axioms gelu_lipschitz_global
end Project.Gelu.Real
