import Project.ProofKit.DyadicUpper
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option exponentiation.threshold 512

namespace Project.ProofKit.DyadicUpper

noncomputable def value (a : Nat) : ℝ := (a : ℝ) / scale

theorem scale_positive : 0 < scale := by decide
theorem real_scale_positive : (0 : ℝ) < scale := by exact_mod_cast scale_positive
theorem nonnegative (a : Nat) : 0 ≤ value a := div_nonneg (Nat.cast_nonneg a) real_scale_positive.le

theorem max_value (a b : Nat) : value (max a b) = max (value a) (value b) := by
  unfold value
  rw [Nat.cast_max, max_div_div_right (le_of_lt real_scale_positive)]

theorem ceiling_le (numerator denominator : Nat) (hd : 0 < denominator) :
    numerator ≤ ceilingDivision numerator denominator * denominator := by
  have hm := Nat.mod_lt (numerator + denominator - 1) hd
  have he := Nat.mod_add_div (numerator + denominator - 1) denominator
  rw [Nat.mul_comm denominator] at he
  unfold ceilingDivision
  omega

theorem integer_value (n : Nat) : value (integer n) = n := by
  simp only [value, integer, Nat.cast_mul]
  exact mul_div_cancel_right₀ _ (ne_of_gt real_scale_positive)

theorem fraction_upper (n d : Nat) (hd : 0 < d) : (n : ℝ) / d ≤ value (fraction n d) := by
  have hs := ceiling_le (n * scale) d hd
  have hr : (n : ℝ) * scale ≤ (fraction n d : ℝ) * d := by exact_mod_cast hs
  exact (div_le_div_iff₀ (by exact_mod_cast hd) real_scale_positive).mpr hr

theorem add_value (a b : Nat) : value (add a b) = value a + value b := by
  simp only [value, add, Nat.cast_add, add_div]

theorem mul_upper (a b : Nat) : value a * value b ≤ value (mul a b) := by
  have hs := ceiling_le (a * b) scale scale_positive
  have hr : (a : ℝ) * b ≤ (mul a b : ℝ) * scale := by exact_mod_cast hs
  unfold value
  rw [div_mul_div_comm]
  apply (div_le_iff₀ (mul_pos real_scale_positive real_scale_positive)).mpr
  calc
    (a : ℝ) * b ≤ (mul a b : ℝ) * scale := hr
    _ = (mul a b : ℝ) / scale * (scale * scale) := by field_simp [ne_of_gt real_scale_positive]

theorem divNat_upper (a d : Nat) (hd : 0 < d) : value a / d ≤ value (divNat a d) := by
  have hs := ceiling_le a d hd
  have hr : (a : ℝ) ≤ (divNat a d : ℝ) * d := by exact_mod_cast hs
  unfold value
  rw [div_div]
  apply (div_le_iff₀ (mul_pos real_scale_positive (by exact_mod_cast hd))).mpr
  calc
    (a : ℝ) ≤ (divNat a d : ℝ) * d := hr
    _ = (divNat a d : ℝ) / scale * (scale * d) := by field_simp [ne_of_gt real_scale_positive]

theorem fp32Magnitude_value (m : Nat) : value (fp32Magnitude m) = (m : ℝ) / 2 ^ 149 := by
  norm_num [value, fp32Magnitude, scale, Nat.cast_mul]
  ring

theorem add_bound (x y : ℝ) (a b : Nat) (hx : x ≤ value a) (hy : y ≤ value b) :
    x + y ≤ value (add a b) := by
  rw [add_value]
  exact add_le_add hx hy

theorem mul_bound (x y : ℝ) (a b : Nat) (hy0 : 0 ≤ y)
    (hx : x ≤ value a) (hy : y ≤ value b) : x * y ≤ value (mul a b) :=
  (mul_le_mul hx hy hy0 (nonnegative a)).trans (mul_upper a b)

theorem mul_bound_left (x y : ℝ) (a b : Nat) (hx0 : 0 ≤ x)
    (hx : x ≤ value a) (hy : y ≤ value b) : x * y ≤ value (mul a b) :=
  ((mul_le_mul_of_nonneg_left hy hx0).trans
    (mul_le_mul_of_nonneg_right hx (nonnegative b))).trans (mul_upper a b)

theorem divNat_bound (x : ℝ) (a d : Nat) (hd : 0 < d) (hx : x ≤ value a) :
    x / d ≤ value (divNat a d) :=
  (div_le_div_of_nonneg_right hx (by exact_mod_cast hd.le)).trans (divNat_upper a d hd)

theorem timesNat_value (a n : Nat) : value (n * a) = (n : ℝ) * value a := by
  simp only [value, Nat.cast_mul, mul_div_assoc]

theorem roundoff_upper (bound subtraction denominatorPower : Nat) :
    (2 : ℝ) ^ (bound - subtraction) / 2 ^ denominatorPower ≤ value (roundoff bound subtraction denominatorPower) := by
  simpa only [roundoff, Nat.cast_pow, Nat.cast_ofNat] using
    fraction_upper (2 ^ (bound - subtraction)) (2 ^ denominatorPower) (by positivity)

#print axioms fraction_upper
#print axioms mul_upper
#print axioms divNat_upper
end Project.ProofKit.DyadicUpper
