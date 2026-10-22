import Library.Numerics.Float64.Sinpi.SinpiProduct
import Library.Numerics.Float64.Tan.TanEven

/-!
The error of `Sinpi.piTiny` in real numbers.  With `A = x 2 ^ 53 = H + L` split into a head and
an exact tail, the sum `(pc L + pl H) + ph H` before its last rounding lies within
`|A| / 2 ^ 65 + 2 ^ -1036` of `π A`.  After the rounding of the sum and the scaling by `2 ^ -53`,
which is exact when its result is normal, the result lies within `(1 + 2 ^ -10) u` of `π x`
relative to the larger of `|π x|` and `2 ^ -1021`, plus `2 ^ -1085`.  `sin y` and `tan y` lie
within `|y| ^ 3` of `y` for `|y| ≤ 1/10`.
-/

namespace Library.Numerics.Float64.Sinpi.SinpiTinyReal

open SinpiProduct

set_option exponentiation.threshold 1200

theorem abs_add4 (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

theorem abs_add5 (a b c d e : ℝ) : |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le (a + b + c + d) e
  have h2 := abs_add4 a b c d
  linarith

/-- The error of the sum before its last rounding. -/
theorem sum_error (A H L p1 p2 a1 : ℝ) (hL : L = A - H)
    (hLb : |L| ≤ |A| / 2 ^ 20 + 1 / 2 ^ 989) (hHb : |H| ≤ |A|)
    (hp1 : |p1 - 7074237752028440 / 2 ^ 51 * L| ≤
      1 / 2 ^ 53 * (|7074237752028440 / 2 ^ 51 * L| + 1 / 2 ^ 1022))
    (hp2 : |p2 - -(8407515482766138 / 2 ^ 78) * H| ≤
      1 / 2 ^ 53 * (|-(8407515482766138 / 2 ^ 78) * H| + 1 / 2 ^ 1022))
    (ha1 : |a1 - (p1 + p2)| ≤ 1 / 2 ^ 53 * |p1 + p2|) :
    |a1 + 52707179 / 2 ^ 24 * H - Real.pi * A| ≤ |A| / 2 ^ 65 + 1 / 2 ^ 1036 := by
  obtain ⟨hpi1, hpi2⟩ := pi_parts
  have key : a1 + 52707179 / 2 ^ 24 * H - Real.pi * A =
      (a1 - (p1 + p2)) + (p1 - 7074237752028440 / 2 ^ 51 * L) +
        (p2 - -(8407515482766138 / 2 ^ 78) * H) + (7074237752028440 / 2 ^ 51 - Real.pi) * L +
        (52707179 / 2 ^ 24 - 8407515482766138 / 2 ^ 78 - Real.pi) * H := by
    rw [hL]; ring
  have hc1 : |(7074237752028440 / 2 ^ 51 : ℝ) * L| = 7074237752028440 / 2 ^ 51 * |L| := by
    rw [abs_mul, abs_of_pos (by positivity)]
  have hc2 : |-(8407515482766138 / 2 ^ 78 : ℝ) * H| = 8407515482766138 / 2 ^ 78 * |H| := by
    rw [abs_mul, abs_neg, abs_of_pos (by positivity)]
  have hsum := abs_add4 (7074237752028440 / 2 ^ 51 * L) (-(8407515482766138 / 2 ^ 78) * H)
    (p1 - 7074237752028440 / 2 ^ 51 * L) (p2 - -(8407515482766138 / 2 ^ 78) * H)
  rw [hc1, hc2, show (7074237752028440 / 2 ^ 51 : ℝ) * L + -(8407515482766138 / 2 ^ 78) * H +
    (p1 - 7074237752028440 / 2 ^ 51 * L) + (p2 - -(8407515482766138 / 2 ^ 78) * H) = p1 + p2 by
    ring] at hsum
  rw [hc1] at hp1
  rw [hc2] at hp2
  have m1 : |(7074237752028440 / 2 ^ 51 : ℝ) - Real.pi| * |L| ≤ 1 / 2 ^ 50 * |L| :=
    mul_le_mul_of_nonneg_right hpi2 (abs_nonneg _)
  have m2 : |(52707179 / 2 ^ 24 : ℝ) - 8407515482766138 / 2 ^ 78 - Real.pi| * |H| ≤
      1 / 2 ^ 66 * |H| := mul_le_mul_of_nonneg_right hpi1 (abs_nonneg _)
  have h5 := abs_add5 (a1 - (p1 + p2)) (p1 - 7074237752028440 / 2 ^ 51 * L)
    (p2 - -(8407515482766138 / 2 ^ 78) * H) ((7074237752028440 / 2 ^ 51 - Real.pi) * L)
    ((52707179 / 2 ^ 24 - 8407515482766138 / 2 ^ 78 - Real.pi) * H)
  rw [← key, abs_mul, abs_mul] at h5
  have hL0 := abs_nonneg L
  have hH0 := abs_nonneg H
  linarith

/-- The result against `π x`. -/
theorem final_error (X A S s r : ℝ) (hA : A = X * 2 ^ 53)
    (hE : |S - Real.pi * A| ≤ |A| / 2 ^ 65 + 1 / 2 ^ 1036)
    (hs : |s - S| ≤ 1 / 2 ^ 53 * |S|)
    (hr1 : 1 / 2 ^ 1022 ≤ |s / 2 ^ 53| → r = s / 2 ^ 53)
    (hr2 : |s / 2 ^ 53| < 1 / 2 ^ 1022 → |r - s / 2 ^ 53| ≤ 1 / 2 ^ 1075) :
    |r - Real.pi * X| ≤ (1 + 1 / 2 ^ 10) * (1 / 2 ^ 53) * max |Real.pi * X| (1 / 2 ^ 1021) +
      1 / 2 ^ 1085 := by
  have hpi := Real.pi_gt_three
  have hAX : |A| = |X| * 2 ^ 53 := by
    rw [hA, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53)]
  have hE' : |S / 2 ^ 53 - Real.pi * X| ≤ |X| / 2 ^ 65 + 1 / 2 ^ 1089 := by
    have e : S / 2 ^ 53 - Real.pi * X = (S - Real.pi * A) / 2 ^ 53 := by
      rw [hA]
      ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53), div_le_iff₀ (by positivity)]
    rw [hAX] at hE
    linarith
  have hs' : |s / 2 ^ 53 - S / 2 ^ 53| ≤ 1 / 2 ^ 53 * |S / 2 ^ 53| := by
    rw [← sub_div, abs_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53)]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hTX : 3 * |X| ≤ |Real.pi * X| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
  have hM1 := le_max_left |Real.pi * X| (1 / 2 ^ 1021)
  have hM2 := le_max_right |Real.pi * X| (1 / 2 ^ 1021)
  have t1 := abs_sub_abs_le_abs_sub (S / 2 ^ 53) (Real.pi * X)
  have t2 := abs_sub_abs_le_abs_sub (Real.pi * X) (S / 2 ^ 53)
  rw [abs_sub_comm (Real.pi * X)] at t2
  have t3 := abs_sub_abs_le_abs_sub (S / 2 ^ 53) (s / 2 ^ 53)
  rw [abs_sub_comm (S / 2 ^ 53)] at t3
  rcases le_or_gt (1 / 2 ^ 1022) |s / 2 ^ 53| with hn | hn
  · rw [hr1 hn]
    have tri := abs_sub_le (s / 2 ^ 53) (S / 2 ^ 53) (Real.pi * X)
    linarith
  · have hr := hr2 hn
    have tri := abs_sub_le r (s / 2 ^ 53) (Real.pi * X)
    have tri2 := abs_sub_le (s / 2 ^ 53) (S / 2 ^ 53) (Real.pi * X)
    linarith

theorem sin_near_pos (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) : |Real.sin y - y| ≤ y ^ 3 := by
  rcases h0.lt_or_eq with h | h
  · have a := Real.sin_le h0
    have b := Real.sin_gt_sub_cube h
    have c := pow_nonneg h0 3
    rw [abs_le]
    constructor <;> linarith
  · rw [← h, Real.sin_zero]; norm_num

theorem tan_near_pos (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1 / 10) : |Real.tan y - y| ≤ y ^ 3 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := y)
  have hy2 : y ^ 2 ≤ 1 / 100 := by nlinarith
  have hcpos : 0 < Real.cos y := by linarith
  have hs := Real.sin_le h0
  have hlow := (Library.Numerics.Float64.Tan.TanEven.tan_bounds y h0 (by linarith)).1
  have hup : Real.tan y ≤ y + y ^ 3 := by
    rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcpos]
    have e1 : 0 ≤ (y + y ^ 3) * (Real.cos y - (1 - y ^ 2 / 2)) :=
      mul_nonneg (by positivity) (by linarith)
    have e2 : 0 ≤ y ^ 3 * (1 - y ^ 2) := mul_nonneg (pow_nonneg h0 3) (by linarith)
    have e3 : Real.sin y * 1 ≤ y := by linarith
    nlinarith
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- `sin y` within `|y| ^ 3` of `y`. -/
theorem sin_near (y : ℝ) (h : |y| ≤ 1 / 10) : |Real.sin y - y| ≤ |y| ^ 3 := by
  rcases le_total 0 y with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    exact sin_near_pos y h0 (by linarith)
  · rw [abs_of_nonpos h0] at h ⊢
    have := sin_near_pos (-y) (by linarith) (by linarith)
    rwa [Real.sin_neg, show -Real.sin y - -y = -(Real.sin y - y) by ring, abs_neg] at this

/-- `tan y` within `|y| ^ 3` of `y`. -/
theorem tan_near (y : ℝ) (h : |y| ≤ 1 / 10) : |Real.tan y - y| ≤ |y| ^ 3 := by
  rcases le_total 0 y with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    exact tan_near_pos y h0 h
  · rw [abs_of_nonpos h0] at h ⊢
    have := tan_near_pos (-y) (by linarith) h
    rwa [Real.tan_neg, show -Real.tan y - -y = -(Real.tan y - y) by ring, abs_neg] at this

#print axioms sum_error
#print axioms final_error
#print axioms sin_near
#print axioms tan_near

end Library.Numerics.Float64.Sinpi.SinpiTinyReal
