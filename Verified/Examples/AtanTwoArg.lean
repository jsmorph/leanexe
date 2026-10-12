import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
`Complex.arg (x + y i)` through `arctan (y / x)`: the angle itself for `x > 0`, and the angle
plus or minus `π` for `x < 0` by the sign of `y`.
-/

namespace Verified.Examples.AtanTwoArg

theorem arg_of_pos (x y : ℝ) (hx : 0 < x) :
    Complex.arg ((x : ℂ) + (y : ℂ) * Complex.I) = Real.arctan (y / x) := by
  set t := y / x with ht
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hr : 0 < x * Real.sqrt (1 + t ^ 2) := mul_pos hx hs
  have hθ : Real.arctan t ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · linarith [Real.neg_pi_div_two_lt_arctan t, Real.pi_pos]
    · linarith [Real.arctan_lt_pi_div_two t, Real.pi_pos]
  have heq : (x : ℂ) + (y : ℂ) * Complex.I =
      ((x * Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) *
        (Complex.cos (Real.arctan t) + Complex.sin (Real.arctan t) * Complex.I) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_arctan, Real.sin_arctan]
    have hne : Real.sqrt (1 + t ^ 2) ≠ 0 := hs.ne'
    have hy : y = x * t := by rw [ht]; field_simp
    apply Complex.ext <;> simp [hy] <;> field_simp
  rw [heq, Complex.arg_mul_cos_add_sin_mul_I hr hθ]

theorem arg_of_neg_of_pos (x y : ℝ) (hx : x < 0) (hy : 0 < y) :
    Complex.arg ((x : ℂ) + (y : ℂ) * Complex.I) = Real.arctan (y / x) + Real.pi := by
  have h := arg_of_pos (-x) (-y) (by linarith)
  have hz : (x : ℂ) + (y : ℂ) * Complex.I = -(((-x : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hz, Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simp; linarith), h, neg_div_neg_eq]

theorem arg_of_neg_of_neg (x y : ℝ) (hx : x < 0) (hy : y < 0) :
    Complex.arg ((x : ℂ) + (y : ℂ) * Complex.I) = Real.arctan (y / x) - Real.pi := by
  have h := arg_of_pos (-x) (-y) (by linarith)
  have hz : (x : ℂ) + (y : ℂ) * Complex.I = -(((-x : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hz, Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by simp; linarith), h, neg_div_neg_eq]

#print axioms arg_of_pos
#print axioms arg_of_neg_of_pos
#print axioms arg_of_neg_of_neg

end Verified.Examples.AtanTwoArg
