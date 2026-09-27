import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Project.Gelu.Real

noncomputable def coefficient : ℝ := 44715 / 1000000
noncomputable def scale : ℝ := Real.sqrt (2 / Real.pi)
noncomputable def argument (x : ℝ) : ℝ := 2 * scale * (x + coefficient * x^3)
noncomputable def gelu (x : ℝ) : ℝ :=
  x * (1 + Real.tanh (scale * (x + coefficient * x^3))) / 2

theorem scale_bounds : 797884/1000000 ≤ scale ∧ scale ≤ 797885/1000000 := by
  have hp := Real.pi_pos
  constructor
  · apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ hp).mpr
    nlinarith only [Real.pi_lt_d6]
  · apply (Real.sqrt_le_left (by norm_num)).mpr
    apply (div_le_iff₀ hp).mpr
    nlinarith only [Real.pi_gt_d6]

theorem scale_bounds_precise :
    7978845608028653/10000000000000000 ≤ scale ∧
    scale ≤ 7978845608028654/10000000000000000 := by
  have hp := Real.pi_pos
  constructor
  · apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    apply (le_div_iff₀ hp).mpr
    nlinarith only [Real.pi_lt_d20]
  · apply (Real.sqrt_le_left (by norm_num)).mpr
    apply (div_le_iff₀ hp).mpr
    nlinarith only [Real.pi_gt_d20]

theorem argument_bounds (a : ℝ) (ha : 0 ≤ a) (hu : a ≤ 3) :
    0 ≤ argument a ∧ argument a ≤ 7 := by
  have hk : 0 ≤ scale ∧ scale ≤ 4/5 := by
    have h := scale_bounds
    constructor <;> linarith
  have hc : 0 ≤ coefficient ∧ coefficient ≤ 9/200 := by
    norm_num [coefficient]
  have ha3 : 0 ≤ a^3 ∧ a^3 ≤ 27 := by
    constructor
    · positivity
    · nlinarith [sq_nonneg (a-3), mul_nonneg ha (sq_nonneg (a-3))]
  have hca := mul_le_mul hc.2 ha3.2 ha3.1 (by norm_num : (0:ℝ) ≤ 9/200)
  unfold argument
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) hk.1)
      (add_nonneg ha (mul_nonneg hc.1 ha3.1))
  · nlinarith [mul_le_mul_of_nonneg_left (show a + coefficient*a^3 ≤ 3 + 9/200*27 by linarith)
      hk.1]

theorem tanh_logistic (t : ℝ) :
    (1 + Real.tanh t) / 2 = 1 / (1 + Real.exp (-2*t)) := by
  have hp := Real.exp_pos t
  have hn := Real.exp_pos (-t)
  have he : Real.exp (-2*t) = Real.exp (-t) / Real.exp t := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [Real.tanh_eq, he]
  field_simp
  ring

theorem gelu_logistic (x : ℝ) :
    gelu x = x / (1 + Real.exp (-argument x)) := by
  unfold gelu argument
  rw [show x * (1 + Real.tanh (scale * (x + coefficient*x^3))) / 2 =
    x * ((1 + Real.tanh (scale * (x + coefficient*x^3))) / 2) by ring]
  rw [tanh_logistic]
  rw [show -(2 * scale * (x + coefficient*x^3)) =
    -2 * (scale * (x + coefficient*x^3)) by ring]
  ring

theorem gelu_neg (x : ℝ) : gelu (-x) = gelu x - x := by
  have h : scale * (-x + coefficient * (-x)^3) =
      -(scale * (x + coefficient * x^3)) := by ring
  simp only [gelu, h, Real.tanh_neg]
  ring

theorem gelu_magnitude (x : ℝ) : |gelu x| ≤ |x| := by
  rw [gelu_logistic, abs_div, abs_of_pos (by positivity : 0 < 1 + Real.exp (-argument x))]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [abs_nonneg x, Real.exp_pos (-argument x)]

#print axioms gelu_logistic
#print axioms gelu_magnitude
end Project.Gelu.Real
