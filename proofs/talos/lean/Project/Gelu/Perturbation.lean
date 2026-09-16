import Project.Gelu.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Project.Gelu.Real

noncomputable def sigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

theorem sigmoid_bounds (x : ℝ) : 0 ≤ sigmoid x ∧ sigmoid x ≤ 1 := by
  unfold sigmoid
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity)).mpr
    linarith [Real.exp_pos (-x)]

theorem sigmoid_derivative (x : ℝ) :
    HasDerivAt sigmoid (Real.exp (-x) / (1 + Real.exp (-x))^2) x := by
  have h := (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).const_add 1).inv
    (by positivity : 1 + Real.exp (-x) ≠ 0)
  change HasDerivAt (fun t => 1 / (1 + Real.exp (-t))) _ x
  simpa [one_div, Pi.inv_def, Function.comp_def] using h

theorem sigmoid_derivative_bound (x : ℝ) :
    |Real.exp (-x) / (1 + Real.exp (-x))^2| ≤ 1/4 := by
  rw [abs_of_pos (by positivity : 0 < Real.exp (-x) / (1 + Real.exp (-x))^2)]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [sq_nonneg (Real.exp (-x) - 1)]

theorem sigmoid_lipschitz (x y : ℝ) : |sigmoid x - sigmoid y| ≤ |x-y|/4 := by
  have ordered (a b : ℝ) (hab : a ≤ b) : |sigmoid b-sigmoid a| ≤ (b-a)/4 := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t (_ : t ∈ Set.Icc a b) => (sigmoid_derivative t).hasDerivWithinAt)
      (fun t (_ : t ∈ Set.Ico a b) => by
        simpa only [Real.norm_eq_abs] using sigmoid_derivative_bound t)
      b ⟨hab, le_refl _⟩
    simpa only [Real.norm_eq_abs, one_div, div_eq_mul_inv, mul_comm, one_mul] using h
  rcases le_total x y with h | h
  · rw [abs_sub_comm, abs_of_nonpos (by linarith : x-y ≤ 0)]
    have hh := ordered x y h
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact ordered y x h

theorem argument_lipschitz (x y : ℝ) (hx : |x| ≤ 3) (hy : |y| ≤ 3) :
    |argument x - argument y| ≤ 4 * |x-y| := by
  have hx2 : |x^2| ≤ 9 := by
    have h := mul_le_mul hx hx (abs_nonneg _) (by norm_num)
    norm_num [sq, abs_mul] at *
    exact h
  have hy2 : |y^2| ≤ 9 := by
    have h := mul_le_mul hy hy (abs_nonneg _) (by norm_num)
    norm_num [sq, abs_mul] at *
    exact h
  have hxy : |x*y| ≤ 9 := by
    rw [abs_mul]
    have h := mul_le_mul hx hy (abs_nonneg _) (by norm_num)
    norm_num at h
    exact h
  have hsum : |x^2+x*y+y^2| ≤ 27 := by
    have h := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hx2 hxy)) hy2)
    linarith only [h]
  have h3 : |x^3-y^3| ≤ 27 * |x-y| := by
    rw [show x^3-y^3 = (x-y)*(x^2+x*y+y^2) by ring, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg (x-y))]
  have hk : |2*scale| ≤ 8/5 := by
    have hb := scale_bounds
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hc : |coefficient| ≤ 9/200 := by norm_num [coefficient]
  rw [show argument x - argument y =
    2*scale*((x-y)+coefficient*(x^3-y^3)) by unfold argument; ring, abs_mul]
  have hb : |(x-y)+coefficient*(x^3-y^3)| ≤ (1+9/200*27)*|x-y| := by
    have hproduct : |coefficient*(x^3-y^3)| ≤ (9/200)*(27*|x-y|) := by
      rw [abs_mul]
      exact mul_le_mul hc h3 (abs_nonneg _) (by norm_num)
    have hh := (abs_add_le (x-y) (coefficient*(x^3-y^3))).trans
      (add_le_add (le_refl _) hproduct)
    nlinarith only [hh]
  have h := mul_le_mul hk hb (abs_nonneg _) (by norm_num)
  nlinarith only [h, abs_nonneg (x-y)]

theorem gelu_lipschitz (x y : ℝ) (hx : |x| ≤ 3) (hy : |y| ≤ 3) :
    |gelu x - gelu y| ≤ 4 * |x-y| := by
  have heq (t : ℝ) : gelu t = t * sigmoid (argument t) := by
    rw [gelu_logistic, sigmoid]
    ring
  have hs := sigmoid_lipschitz (argument x) (argument y)
  have ha := argument_lipschitz x y hx hy
  have hd : |sigmoid (argument x)-sigmoid (argument y)| ≤ |x-y| := by linarith
  have hsy : |sigmoid (argument y)| ≤ 1 := by
    rw [abs_of_nonneg (sigmoid_bounds _).1]
    exact (sigmoid_bounds _).2
  rw [heq x, heq y, show x*sigmoid (argument x)-y*sigmoid (argument y) =
    x*(sigmoid (argument x)-sigmoid (argument y))+(x-y)*sigmoid (argument y) by ring]
  have h1 : |x*(sigmoid (argument x)-sigmoid (argument y))| ≤ 3*|x-y| := by
    rw [abs_mul]
    exact mul_le_mul hx hd (abs_nonneg _) (by norm_num)
  have h2 : |(x-y)*sigmoid (argument y)| ≤ |x-y| := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hsy (abs_nonneg (x-y))]
  exact (abs_add_le _ _).trans (by linarith)

#print axioms gelu_lipschitz
end Project.Gelu.Real
