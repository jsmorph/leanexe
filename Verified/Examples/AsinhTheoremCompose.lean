import Verified.Examples.Log1pTheoremNear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Composition of `Log1pTheoremNear.log1p_near` with the error of a computed argument, for the
`log1p` branches of `asinh`, `acosh`, and `atanh`.  `near_compose` moves the target from
`log (1 + w)` to `log (1 + W)` at the cost `|w - W|/m` for `m ≤ 1 + w, 1 + W`.  `log_pade` bounds
`log (1 + W)` from below by `2 W/(2 + W)`, the first term of the series of `log (1 + 1/a)`.
`quad_le` states that a quadratic with a nonnegative leading coefficient lies below 0 on an interval
when it does at the endpoints, which reduces the bounds of each input range to two numeric checks.
-/

namespace Verified.Examples.AsinhTheoremCompose
open CodeLib.IEEE64 LeanExe.ProofKit F64Near

theorem log_pade (W : ℝ) (hW : 0 < W) : 2 * W / (2 + W) ≤ Real.log (1 + W) := by
  have hi : 0 < W⁻¹ := inv_pos.mpr hW
  have hd : 0 < 2 * W⁻¹ + 1 := by linarith
  have h := Real.hasSum_log_one_add_inv hi
  have hs := sum_le_hasSum {0} (fun i _ => mul_nonneg (mul_nonneg (by norm_num) (by positivity))
    (pow_nonneg (le_of_lt (div_pos one_pos hd)) _)) h
  simp only [Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_add, div_one, pow_one, inv_inv,
    mul_one] at hs
  calc 2 * W / (2 + W) = 2 * (1 / (2 * W⁻¹ + 1)) := by
        field_simp
    _ ≤ _ := hs

theorem log_diff (w W m : ℝ) (hm : 0 < m) (hw : m ≤ 1 + w) (hW : m ≤ 1 + W) :
    |Real.log (1 + w) - Real.log (1 + W)| ≤ |w - W| / m := by
  have h1 : 0 < 1 + w := by linarith
  have h2 : 0 < 1 + W := by linarith
  rw [abs_le]
  constructor
  · have h3 := Real.log_le_sub_one_of_pos (div_pos h2 h1)
    rw [Real.log_div h2.ne' h1.ne'] at h3
    have h4 : (1 + W) / (1 + w) - 1 = (W - w) / (1 + w) := by
      field_simp
      ring
    have h5 : (W - w) / (1 + w) ≤ |w - W| / m := by
      rw [abs_sub_comm]
      calc (W - w) / (1 + w) ≤ |W - w| / (1 + w) :=
            div_le_div_of_nonneg_right (le_abs_self _) h1.le
        _ ≤ |W - w| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hw
    linarith
  · have h3 := Real.log_le_sub_one_of_pos (div_pos h1 h2)
    rw [Real.log_div h1.ne' h2.ne'] at h3
    have h4 : (1 + w) / (1 + W) - 1 = (w - W) / (1 + W) := by
      field_simp
      ring
    have h5 : (w - W) / (1 + W) ≤ |w - W| / m :=
      calc (w - W) / (1 + W) ≤ |w - W| / (1 + W) :=
            div_le_div_of_nonneg_right (le_abs_self _) h2.le
        _ ≤ |w - W| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hW
    linarith

/-- The bound at the computed argument `w` moves to the exact argument `W`. -/
theorem near_compose {c : UInt64} {w W E δ m : ℝ} (h : Near c (Real.log (1 + w)) E)
    (hd : |w - W| ≤ δ) (hm : 0 < m) (hw : m ≤ 1 + w) (hW : m ≤ 1 + W) :
    Near c (Real.log (1 + W)) (E + δ / m) := by
  refine (h.shift _).mono ?_
  have h1 := log_diff w W m hm hw hW
  have h2 : |w - W| / m ≤ δ / m := div_le_div_of_nonneg_right hd hm.le
  linarith

/-- A quadratic with a nonnegative leading coefficient is at most 0 between two points where it
is at most 0. -/
theorem quad_le (α β γ L H a : ℝ) (hα : 0 ≤ α) (hL : L ≤ a) (hH : a ≤ H)
    (h1 : α * L ^ 2 + β * L + γ ≤ 0) (h2 : α * H ^ 2 + β * H + γ ≤ 0) :
    α * a ^ 2 + β * a + γ ≤ 0 := by
  have h3 : α * a ^ 2 ≤ α * ((L + H) * a - L * H) := by
    apply mul_le_mul_of_nonneg_left _ hα
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hH)]
  have h4 : (H - L) * (α * ((L + H) * a - L * H) + β * a + γ) =
      (H - a) * (α * L ^ 2 + β * L + γ) + (a - L) * (α * H ^ 2 + β * H + γ) := by ring
  have h5 : (H - L) * (α * ((L + H) * a - L * H) + β * a + γ) ≤ 0 := by
    rw [h4]
    nlinarith [mul_nonneg (sub_nonneg.mpr hH) (neg_nonneg.mpr h1),
      mul_nonneg (sub_nonneg.mpr hL) (neg_nonneg.mpr h2)]
  rcases eq_or_lt_of_le (hL.trans hH) with hLH | hLH
  · have ha : a = L := le_antisymm (hLH ▸ hH) hL
    rw [ha]
    exact h1
  · have h6 : α * ((L + H) * a - L * H) + β * a + γ ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos (sub_pos.mpr hLH) hc
      linarith
    linarith

theorem errQuad_le (v E : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 285 / 1000)
    (hE : 174 / 100 / 2 ^ 53 * (285 / 1000) ^ 2 + 285 / 1000 / 2 ^ 59 ≤ E) :
    174 / 100 / 2 ^ 53 * v ^ 2 + v / 2 ^ 59 ≤ E := by
  have h2 : v ^ 2 ≤ (285 / 1000) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : 174 / 100 / 2 ^ 53 * v ^ 2 ≤ 174 / 100 / 2 ^ 53 * (285 / 1000) ^ 2 :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  have h4 : v / 2 ^ 59 ≤ 285 / 1000 / 2 ^ 59 := div_le_div_of_nonneg_right h1 (by norm_num)
  linarith

theorem errBound_mid (v : ℝ) (h1 : 6499 / 10000 ≤ v) (h2 : v < 2 ^ 53) :
    Log1pTheoremNear.errBound v = 133 / 100 / 2 ^ 54 := by
  have e1 : ¬ v ≤ 285 / 1000 := by intro h; linarith
  have e2 : ¬ v < 868669 / 2097152 := by intro h; linarith
  have e3 : ¬ v < 4999 / 10000 := by intro h; linarith
  have e4 : ¬ v < 5603 / 10000 := by intro h; linarith
  have e5 : ¬ v < 6499 / 10000 := by intro h; linarith
  rw [Log1pTheoremNear.errBound, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5,
    if_pos h2]

theorem errBound_big (v : ℝ) (h : 2 ^ 53 ≤ v) : Log1pTheoremNear.errBound v = 6 / 2 ^ 54 := by
  have h0 : (6499 : ℝ) / 10000 < 2 ^ 53 := by norm_num
  have e1 : ¬ v ≤ 285 / 1000 := by intro h'; linarith
  have e2 : ¬ v < 868669 / 2097152 := by intro h'; linarith
  have e3 : ¬ v < 4999 / 10000 := by intro h'; linarith
  have e4 : ¬ v < 5603 / 10000 := by intro h'; linarith
  have e5 : ¬ v < 6499 / 10000 := by intro h'; linarith
  rw [Log1pTheoremNear.errBound, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5,
    if_neg (not_lt.mpr h)]

#print axioms log_pade
#print axioms log_diff
#print axioms near_compose
#print axioms quad_le

end Verified.Examples.AsinhTheoremCompose
