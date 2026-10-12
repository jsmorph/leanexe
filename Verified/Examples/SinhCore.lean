import Verified.Examples.SinhWords

/-!
Real bounds for `sinh` below 22.  With `τ = exp a - 1`, `2 sinh a = f τ` for
`f z = z + z/(1 + z)` (`two_sinh`), and `f T - f τ = (T - τ)(1 + 1/((1 + T)(1 + τ)))`
(`f_diff`), so an error `E` of `T = expm1 a` enters `2 sinh a` with a factor below 2.  The code
evaluates `f T` as `2 T - T T/(T + 1)` below 1 and as `T + T/(T + 1)` above; the rounded
quotients lie within `3.1 u` and `2.1 u` of `T T/(1 + T)` and `T/(1 + T)` (`small_round`,
`mid_round`).  `check_small` turns bounds on an interval of `τ` into the relative error
`2.9375 u` that `F64NearestRelative.within_rel_of` needs for three steps.
-/

namespace Verified.Examples.SinhCore
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem f_diff (T τ : ℝ) (hT : 0 < 1 + T) (hτ : 0 < 1 + τ) :
    (T + T / (1 + T)) - (τ + τ / (1 + τ)) = (T - τ) * (1 + 1 / ((1 + T) * (1 + τ))) := by
  field_simp
  ring

theorem two_sinh (A : ℝ) :
    2 * Real.sinh A = (Real.exp A - 1) + (Real.exp A - 1) / (1 + (Real.exp A - 1)) := by
  have h := Real.exp_pos A
  rw [Real.sinh_eq, Real.exp_neg, show 1 + (Real.exp A - 1) = Real.exp A by ring]
  field_simp
  ring

/-- The rounded `T T / (T + 1)`. -/
theorem small_round (T p d q : ℝ) (hT0 : 1 / 2 ^ 30 ≤ T) (hT1 : T ≤ 2)
    (hp : |p - T * T| ≤ u * |T * T| + η) (hd : |d - (1 + T)| ≤ u * |1 + T|)
    (hq : |q - p / d| ≤ u * |p / d| + η) :
    |q - T * T / (1 + T)| ≤ 31 / 10 * u * (T * T / (1 + T)) := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have hT0' : 0 < T := lt_of_lt_of_le (by positivity) hT0
  have h1T : 0 < 1 + T := by linarith
  rw [abs_of_pos (mul_pos hT0' hT0'), hu, hη] at hp
  rw [abs_of_pos h1T, hu] at hd
  rw [hu, hη] at hq
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd
  have hd0 : (1 + T) * (1 - 1 / 2 ^ 53) ≤ d := by linarith
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hd0
  set Q := T * T / (1 + T) with hQdef
  have hQ : Q * (1 + T) = T * T := by rw [hQdef]; field_simp
  have hQ0 : 0 < Q := by rw [hQdef]; positivity
  have hQlo : T * T / 3 ≤ Q := by
    rw [hQdef]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hTT : 1 / 2 ^ 60 ≤ T * T := by
    have := mul_le_mul hT0 hT0 (by positivity) hT0'.le
    have h2 : (1 : ℝ) / 2 ^ 60 = 1 / 2 ^ 30 * (1 / 2 ^ 30) := by norm_num
    linarith
  set r := p / d with hrdef
  have hr : r * d = p := by rw [hrdef]; exact div_mul_cancel₀ p hdpos.ne'
  have hkey : (r - Q) * d = (p - T * T) - Q * (d - (1 + T)) := by
    linear_combination hr - hQ
  have hA : |r - Q| * ((1 + T) * (1 - 1 / 2 ^ 53)) ≤ 2 / 2 ^ 53 * (T * T) + 1 / 2 ^ 1075 := by
    have h1 : |r - Q| * d = |(p - T * T) - Q * (d - (1 + T))| := by
      rw [← hkey, abs_mul, abs_of_pos hdpos]
    have h2 : |(p - T * T) - Q * (d - (1 + T))| ≤ |p - T * T| + Q * |d - (1 + T)| := by
      calc |(p - T * T) - Q * (d - (1 + T))| ≤ |p - T * T| + |Q * (d - (1 + T))| := abs_sub _ _
        _ = |p - T * T| + Q * |d - (1 + T)| := by rw [abs_mul, abs_of_pos hQ0]
    have h3 : Q * |d - (1 + T)| ≤ Q * (1 / 2 ^ 53 * (1 + T)) :=
      mul_le_mul_of_nonneg_left hd hQ0.le
    have h4 : Q * (1 / 2 ^ 53 * (1 + T)) = 1 / 2 ^ 53 * (T * T) := by
      linear_combination (1 / 2 ^ 53) * hQ
    calc |r - Q| * ((1 + T) * (1 - 1 / 2 ^ 53)) ≤ |r - Q| * d :=
          mul_le_mul_of_nonneg_left hd0 (abs_nonneg _)
      _ ≤ 2 / 2 ^ 53 * (T * T) + 1 / 2 ^ 1075 := by rw [h1]; linarith
  -- Divide by `1 + T`.
  have hB : |r - Q| * (1 - 1 / 2 ^ 53) ≤ 2 / 2 ^ 53 * Q + 1 / 2 ^ 1075 := by
    have h5 : (2 / 2 ^ 53 * (T * T) + 1 / 2 ^ 1075) ≤
        (2 / 2 ^ 53 * Q + 1 / 2 ^ 1075) * (1 + T) := by
      have : (0 : ℝ) ≤ 1 / 2 ^ 1075 * T := by positivity
      nlinarith [hQ]
    have h6 : |r - Q| * (1 - 1 / 2 ^ 53) * (1 + T) ≤ (2 / 2 ^ 53 * Q + 1 / 2 ^ 1075) * (1 + T) := by
      nlinarith [hA, h5]
    exact le_of_mul_le_mul_right h6 h1T
  have hC : |r - Q| ≤ 20001 / 10000 * (1 / 2 ^ 53) * Q + 2 / 2 ^ 1075 := by
    have : (0 : ℝ) ≤ |r - Q| := abs_nonneg _
    nlinarith
  have hrabs : |r| ≤ Q + |r - Q| := by
    calc |r| = |Q + (r - Q)| := by ring_nf
      _ ≤ |Q| + |r - Q| := abs_add_le _ _
      _ = Q + |r - Q| := by rw [abs_of_pos hQ0]
  have hη2 : (1 : ℝ) / 2 ^ 1075 * 10 ≤ 1 / 100 * (1 / 2 ^ 53) * Q := by
    have : (1 : ℝ) / 2 ^ 1075 * 10 ≤ 1 / 100 * (1 / 2 ^ 53) * (1 / 2 ^ 60 / 3) := by norm_num
    nlinarith
  calc |q - Q| ≤ |q - r| + |r - Q| := abs_sub_le _ _ _
    _ ≤ (1 / 2 ^ 53 * |r| + 1 / 2 ^ 1075) + |r - Q| := add_le_add hq le_rfl
    _ ≤ 31 / 10 * (1 / 2 ^ 53) * Q := by
        have := mul_le_mul_of_nonneg_left hrabs (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 53)
        nlinarith

/-- The rounded `T / (T + 1)`. -/
theorem mid_round (T d r : ℝ) (hT0 : 1 ≤ T) (hd : |d - (1 + T)| ≤ u * |1 + T|)
    (hr : |r - T / d| ≤ u * |T / d| + η) :
    |r - T / (1 + T)| ≤ 21 / 10 * u * (T / (1 + T)) := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have h1T : 0 < 1 + T := by linarith
  rw [abs_of_pos h1T, hu] at hd
  rw [hu, hη] at hr
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd
  have hd0 : (1 + T) * (1 - 1 / 2 ^ 53) ≤ d := by linarith
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hd0
  set R := T / (1 + T) with hRdef
  have hR : R * (1 + T) = T := by rw [hRdef]; field_simp
  have hR0 : 1 / 2 ≤ R := by
    rw [hRdef, le_div_iff₀ h1T]; linarith
  have hR1 : R ≤ 1 := by rw [hRdef, div_le_one h1T]; linarith
  set s := T / d with hsdef
  have hs : s * d = T := by rw [hsdef]; exact div_mul_cancel₀ T hdpos.ne'
  have hkey : (s - R) * d = -(R * (d - (1 + T))) := by linear_combination hs - hR
  have hA : |s - R| * ((1 + T) * (1 - 1 / 2 ^ 53)) ≤ R * (1 / 2 ^ 53 * (1 + T)) := by
    have h1 : |s - R| * d = R * |d - (1 + T)| := by
      rw [← abs_of_pos hdpos, ← abs_mul, hkey, abs_neg, abs_mul, abs_of_pos (by linarith : 0 < R),
        abs_of_pos hdpos]
    calc |s - R| * ((1 + T) * (1 - 1 / 2 ^ 53)) ≤ |s - R| * d :=
          mul_le_mul_of_nonneg_left hd0 (abs_nonneg _)
      _ = R * |d - (1 + T)| := h1
      _ ≤ R * (1 / 2 ^ 53 * (1 + T)) := mul_le_mul_of_nonneg_left hd (by linarith)
  have hB : |s - R| * (1 - 1 / 2 ^ 53) ≤ 1 / 2 ^ 53 * R := by
    have h6 : |s - R| * (1 - 1 / 2 ^ 53) * (1 + T) ≤ 1 / 2 ^ 53 * R * (1 + T) := by
      nlinarith [hA]
    exact le_of_mul_le_mul_right h6 h1T
  have hC : |s - R| ≤ 10001 / 10000 * (1 / 2 ^ 53) * R := by
    have : (0 : ℝ) ≤ |s - R| := abs_nonneg _
    nlinarith
  have hsabs : |s| ≤ R + |s - R| := by
    calc |s| = |R + (s - R)| := by ring_nf
      _ ≤ |R| + |s - R| := abs_add_le _ _
      _ = R + |s - R| := by rw [abs_of_pos (by linarith)]
  calc |r - R| ≤ |r - s| + |s - R| := abs_sub_le _ _ _
    _ ≤ (1 / 2 ^ 53 * |s| + 1 / 2 ^ 1075) + |s - R| := add_le_add hr le_rfl
    _ ≤ 21 / 10 * (1 / 2 ^ 53) * R := by
        have := mul_le_mul_of_nonneg_left hsabs (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 53)
        have h7 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 100 * (1 / 2 ^ 53) * (1 / 2) := by norm_num
        nlinarith

/-- From bounds on an interval `[lo, hi]` of `τ`, an error `E ≤ e` of `T` gives the relative error
`2.9375 u` of `2 T - T T/(1 + T)`. -/
theorem check_small (τ T E lo hi e c1 c2 c3 : ℝ) (hlo0 : 0 ≤ lo) (hlo : lo ≤ τ) (hhi : τ ≤ hi)
    (hE : E ≤ e) (hT : |T - τ| ≤ E) (hle : e < lo)
    (hc1 : 1 / ((1 + lo - e) * (1 + lo)) ≤ c1)
    (hc2 : (hi + e) * (hi + e) / (1 + hi + e) ≤ c2) (hc3 : c3 ≤ lo + lo / (1 + lo))
    (hnum : e * (1 + c1) + 31 / 10 * u * c2 ≤ 2.9375 * u * c3) :
    E * (1 + 1 / ((1 + T) * (1 + τ))) + 31 / 10 * u * (T * T / (1 + T)) ≤
      2.9375 * u * (τ + τ / (1 + τ)) := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ u := by rw [hu]; positivity
  obtain ⟨hT1, hT2⟩ := abs_le.mp hT
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) hT
  have hTlo : lo - e ≤ T := by linarith
  have hThi : T ≤ hi + e := by linarith
  have hT0 : 0 < T := by linarith
  have h1 : 1 / ((1 + T) * (1 + τ)) ≤ c1 := by
    refine le_trans ?_ hc1
    apply one_div_le_one_div_of_le (by nlinarith)
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have h2 : T * T / (1 + T) ≤ c2 := by
    refine le_trans ?_ hc2
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have hH : 0 < hi + e := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hThi)
      (add_nonneg (add_nonneg hH.le hT0.le) (mul_nonneg hH.le hT0.le))]
  have h3 : lo + lo / (1 + lo) ≤ τ + τ / (1 + τ) := by
    have : lo / (1 + lo) ≤ τ / (1 + τ) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith
  have h4 : E * (1 + 1 / ((1 + T) * (1 + τ))) ≤ e * (1 + c1) := by
    have : 0 ≤ 1 / ((1 + T) * (1 + τ)) := by
      apply div_nonneg zero_le_one; nlinarith
    exact mul_le_mul hE (by linarith) (by linarith) (by linarith)
  have h5 : 31 / 10 * u * (T * T / (1 + T)) ≤ 31 / 10 * u * c2 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h6 : 2.9375 * u * c3 ≤ 2.9375 * u * (τ + τ / (1 + τ)) :=
    mul_le_mul_of_nonneg_left (hc3.trans h3) (by positivity)
  linarith

#print axioms f_diff
#print axioms two_sinh
#print axioms small_round
#print axioms mid_round
#print axioms check_small

end Verified.Examples.SinhCore
