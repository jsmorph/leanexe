import LeanExe.ProofKit.GammaBasic
import LeanExe.ProofKit.PolyBound

/-!
Lower bounds on `|log |Γ x||` where `Lgamma.accurate` keeps a pair with an absolute error and
no polynomial about a zero applies.  At negative arguments: `(-2, -1/4]` (`lower_neg`), the
half-integers from `-19/2` to `-7/2` (`lower_half`), and the double `sxBound` nearest -2.61
(`lower_sxb`).  At the positive windows about 0.5, 1.5, 2.5, and 3.5: `pos_quarter`, `pos_mid`,
and `pos_large`, each at least `1/20`.  The bounds come from `Γ s = Γ (s + n) / ∏ (s + j)` with `s + n` in `[1, 2]`,
where the convexity of `Γ` and `Γ (3/2) = √π/2` give `Γ ≥ 3/4` (`gamma_lower`), `Γ ≥ 0.8275`
on `[5/4, 7/4]` (`gamma_lower_mid`), and the chords through `1`, `3/2`, and `2` from above
(`gamma_upper`, `gamma_upper2`).
-/

namespace Verified.Examples.LgammaAccLower
open Real LeanExe.ProofKit GammaBasic Finset

theorem gamma_three_halves : Gamma (3 / 2) = √π / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Gamma_add_one (by norm_num), Gamma_one_half_eq]
  ring

theorem gamma_three_halves_bounds : 885 / 1000 ≤ Gamma (3 / 2) ∧ Gamma (3 / 2) ≤ 8863 / 10000 := by
  rw [gamma_three_halves]
  have h1 : (177 / 100 : ℝ) ≤ √π := by
    rw [le_sqrt (by norm_num) pi_pos.le]
    have := pi_gt_d2
    norm_num at this ⊢
    linarith
  have h2 : √π ≤ 17726 / 10000 := by
    rw [sqrt_le_left (by norm_num)]
    have := pi_lt_d4
    norm_num at this ⊢
    linarith
  constructor <;> linarith

/-- **`Γ` on `[1, 2]` from below**, by the secants through `3/2`. -/
theorem gamma_lower_abs (u : ℝ) (h1 : 1 ≤ u) (h2 : u ≤ 2) :
    Gamma (3 / 2) - 2 * (1 - Gamma (3 / 2)) * |u - 3 / 2| ≤ Gamma u := by
  obtain ⟨g1, g2⟩ := gamma_three_halves_bounds
  have hmem : u ∈ Set.Ioi (0 : ℝ) := by rw [Set.mem_Ioi]; linarith
  rcases lt_trichotomy u (3 / 2) with hu | hu | hu
  · have hs := convexOn_Gamma.secant_mono (a := 3 / 2) (x := u) (y := 2)
      (by norm_num) hmem (by norm_num) hu.ne (by norm_num) (by linarith)
    rw [Gamma_two, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] at hs
    have hneg : u - 3 / 2 < 0 := by linarith
    rw [div_le_iff_of_neg hneg] at hs
    have : (1 - Gamma (3 / 2)) / (1 / 2) * (u - 3 / 2) =
        2 * (1 - Gamma (3 / 2)) * (u - 3 / 2) := by ring
    rw [abs_of_neg hneg]
    nlinarith
  · rw [hu, sub_self, abs_zero, mul_zero, sub_zero]
  · have hs := convexOn_Gamma.secant_mono (a := 3 / 2) (x := 1) (y := u)
      (by norm_num) (by norm_num) hmem (by norm_num) hu.ne' (by linarith)
    rw [Gamma_one, show (1 : ℝ) - 3 / 2 = -(1 / 2) by norm_num] at hs
    have hpos : 0 < u - 3 / 2 := by linarith
    rw [le_div_iff₀ hpos] at hs
    have : (1 - Gamma (3 / 2)) / -(1 / 2) * (u - 3 / 2) =
        -(2 * (1 - Gamma (3 / 2)) * (u - 3 / 2)) := by ring
    rw [abs_of_pos hpos]
    nlinarith

/-- **`Γ ≥ 3/4` on `[1, 2]`.** -/
theorem gamma_lower (u : ℝ) (h1 : 1 ≤ u) (h2 : u ≤ 2) : 3 / 4 ≤ Gamma u := by
  obtain ⟨g1, g2⟩ := gamma_three_halves_bounds
  have h := gamma_lower_abs u h1 h2
  have ha : |u - 3 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  nlinarith [mul_le_mul_of_nonneg_left ha (by linarith : (0 : ℝ) ≤ 2 * (1 - Gamma (3 / 2)))]

/-- **`Γ ≥ 0.8275` on `[5/4, 7/4]`.** -/
theorem gamma_lower_mid (u : ℝ) (h1 : 5 / 4 ≤ u) (h2 : u ≤ 7 / 4) : 8275 / 10000 ≤ Gamma u := by
  obtain ⟨g1, g2⟩ := gamma_three_halves_bounds
  have h := gamma_lower_abs u (by linarith) (by linarith)
  have ha : |u - 3 / 2| ≤ 1 / 4 := by rw [abs_le]; constructor <;> linarith
  nlinarith [mul_le_mul_of_nonneg_left ha (by linarith : (0 : ℝ) ≤ 2 * (1 - Gamma (3 / 2)))]

/-- **The chord through `1` and `3/2`** bounds `Γ` on `[1, 3/2]`. -/
theorem gamma_upper (u : ℝ) (h1 : 1 < u) (h2 : u ≤ 3 / 2) :
    Gamma u ≤ 1 - 2274 / 10000 * (u - 1) := by
  obtain ⟨-, g2⟩ := gamma_three_halves_bounds
  have hmem : u ∈ Set.Ioi (0 : ℝ) := by rw [Set.mem_Ioi]; linarith
  have hs := convexOn_Gamma.secant_mono (a := 1) (x := u) (y := 3 / 2)
    (by norm_num) hmem (by norm_num) h1.ne' (by norm_num) h2
  rw [Gamma_one, show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at hs
  have hpos : 0 < u - 1 := by linarith
  rw [div_le_iff₀ hpos] at hs
  have : (Gamma (3 / 2) - 1) / (1 / 2) * (u - 1) = 2 * (Gamma (3 / 2) - 1) * (u - 1) := by ring
  nlinarith [mul_nonneg hpos.le (by linarith : (0 : ℝ) ≤ 8863 / 10000 - Gamma (3 / 2))]

/-- **The chord through `3/2` and `2`** bounds `Γ` on `[3/2, 2]`. -/
theorem gamma_upper2 (u : ℝ) (h1 : 3 / 2 ≤ u) (h2 : u < 2) :
    Gamma u ≤ 1 - 2274 / 10000 * (2 - u) := by
  obtain ⟨-, g2⟩ := gamma_three_halves_bounds
  rcases h1.lt_or_eq with h1 | h1
  · have hmem : u ∈ Set.Ioi (0 : ℝ) := by rw [Set.mem_Ioi]; linarith
    have hs := convexOn_Gamma.secant_mono (a := 2) (x := 3 / 2) (y := u)
      (by norm_num) (by norm_num) hmem (by norm_num) h2.ne h1.le
    rw [Gamma_two, show (3 / 2 : ℝ) - 2 = -(1 / 2) by norm_num] at hs
    have hneg : u - 2 < 0 := by linarith
    rw [le_div_iff_of_neg hneg] at hs
    have : (Gamma (3 / 2) - 1) / -(1 / 2) * (u - 2) = 2 * (Gamma (3 / 2) - 1) * (2 - u) := by
      ring
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - u)
      (by linarith : (0 : ℝ) ≤ 8863 / 10000 - Gamma (3 / 2))]
  · rw [← h1]
    linarith

theorem log_ge_of_ge (y : ℝ) (hy : 3 / 2 ≤ y) : 1 / 4 ≤ Real.log y := by
  have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < y)
  have : y⁻¹ ≤ 2 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  linarith

theorem log_ge_of_ge' (y : ℝ) (hy : 11 / 10 ≤ y) : 1 / 11 ≤ Real.log y := by
  have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < y)
  have : y⁻¹ ≤ 10 / 11 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  linarith

theorem log_le_of_le (y : ℝ) (hy0 : 0 < y) (hy : y ≤ 9 / 10) : Real.log y ≤ -(1 / 16) := by
  have := Real.log_le_sub_one_of_pos hy0
  linarith

/-- **From -2 to -1/4**: `|Γ s| ≥ 3/2`, so `|log |Γ s|| ≥ 1/4`. -/
theorem lower_neg (s : ℝ) (h1 : -2 < s) (h2 : s ≤ -1 / 4) (hint : ∀ n : ℤ, s ≠ n) :
    1 / 4 ≤ |lgamma s| := by
  have hp : NotPole s := notPole_of_not_int hint
  have hs1 : s ≠ -1 := fun h => hint (-1) (by rw [h]; norm_num)
  have hA : 3 / 2 ≤ |Gamma s| := by
    rcases lt_or_gt_of_ne hs1 with hlt | hgt
    · rw [gamma_eq_div hp 3]
      simp only [prod_range_succ, prod_range_zero, one_mul, Nat.cast_ofNat, Nat.cast_one,
        Nat.cast_zero, add_zero]
      have hG := gamma_lower (s + 3) (by linarith) (by linarith)
      have hP : |s * (s + 1) * (s + 2)| ≤ 1 / 2 := by
        rw [abs_mul, abs_mul, abs_of_neg (by linarith : s < 0),
          abs_of_neg (by linarith : s + 1 < 0), abs_of_pos (by linarith : 0 < s + 2)]
        have e1 : -(s + 1) * (s + 2) ≤ 1 / 4 := by nlinarith [sq_nonneg (s + 3 / 2)]
        have e2 : 0 ≤ -(s + 1) * (s + 2) := mul_nonneg (by linarith) (by linarith)
        linarith [mul_le_mul (by linarith : -s ≤ 2) e1 e2 (by norm_num : (0 : ℝ) ≤ 2)]
      have hP0 : 0 < |s * (s + 1) * (s + 2)| := by
        rw [abs_pos]
        exact mul_ne_zero (mul_ne_zero (by linarith) (by linarith)) (by linarith)
      rw [abs_div, abs_of_pos (by linarith : 0 < Gamma (s + 3)), le_div_iff₀ hP0]
      linarith
    · rw [gamma_eq_div hp 2]
      simp only [prod_range_succ, prod_range_zero, one_mul, Nat.cast_ofNat, Nat.cast_one,
        Nat.cast_zero, add_zero]
      have hG := gamma_lower (s + 2) (by linarith) (by linarith)
      have hP : |s * (s + 1)| ≤ 1 / 4 := by
        rw [abs_mul, abs_of_neg (by linarith : s < 0), abs_of_pos (by linarith : 0 < s + 1)]
        nlinarith [sq_nonneg (s + 1 / 2)]
      have hP0 : 0 < |s * (s + 1)| := by
        rw [abs_pos]
        exact mul_ne_zero (by linarith) (by linarith)
      rw [abs_div, abs_of_pos (by linarith : 0 < Gamma (s + 2)), le_div_iff₀ hP0]
      linarith
  unfold lgamma
  rw [← Real.log_abs]
  have := log_ge_of_ge _ hA
  rw [abs_of_pos (by linarith)]
  exact this

/-- **The half-integers from -19/2 to -7/2**: `|Γ s| ≤ 2/7`, so `|log |Γ s|| ≥ 1/16`. -/
theorem lower_half (k : ℕ) (hk3 : 3 ≤ k) (hk9 : k ≤ 9) :
    1 / 16 ≤ |lgamma (-(k : ℝ) - 1 / 2)| := by
  set s : ℝ := -(k : ℝ) - 1 / 2 with hsdef
  have hint : ∀ n : ℤ, s ≠ n := by
    intro n h
    have h2 : (2 * n : ℝ) = -(2 * k + 1 : ℕ) := by rw [← h, hsdef]; push_cast; ring
    have h3 : 2 * n = -((2 * k + 1 : ℕ) : ℤ) := by exact_mod_cast h2
    omega
  have hp : NotPole s := notPole_of_not_int hint
  have hG : Gamma s = √π / ∏ j ∈ range (k + 1), (s + j) := by
    rw [gamma_eq_div hp (k + 1)]
    congr 1
    rw [hsdef, show -(k : ℝ) - 1 / 2 + ((k + 1 : ℕ) : ℝ) = 1 / 2 by push_cast; ring,
      Gamma_one_half_eq]
  have hP : 13 / 2 ≤ |∏ j ∈ range (k + 1), (s + j)| := by
    rw [le_abs, hsdef]
    interval_cases k <;> norm_num [prod_range_succ]
  have hsq : √π ≤ 9 / 5 := by
    rw [sqrt_le_left (by norm_num)]
    have := pi_lt_d2
    norm_num at this ⊢
    linarith
  have hA : |Gamma s| ≤ 2 / 7 := by
    rw [hG, abs_div, abs_of_nonneg (sqrt_nonneg _),
      div_le_iff₀ (lt_of_lt_of_le (by norm_num) hP)]
    linarith
  have hA0 : 0 < |Gamma s| := by
    rw [abs_pos, hG]
    exact div_ne_zero (sqrt_ne_zero'.mpr pi_pos) (shift_prod_ne_zero hp _)
  unfold lgamma
  rw [← Real.log_abs]
  have := log_le_of_le _ hA0 (by linarith)
  rw [abs_of_neg (by linarith)]
  linarith

/-- **At `sxBound`**, the double nearest -2.61: `|Γ| ≤ 0.912`, so `|log |Γ|| ≥ 1/16`. -/
theorem lower_sxb :
    1 / 16 ≤ |lgamma ((PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ)| := by
  have hw : PolyBound.ratOfWord 0xC004E147AE147AE1 = -5877197513718497 / 2 ^ 51 := by
    decide +kernel
  rw [hw]
  push_cast
  generalize hsdef : (-5877197513718497 / 2 ^ 51 : ℝ) = s
  have hint : ∀ n : ℤ, s ≠ n := by
    intro n h
    have h1 : (-3 : ℝ) < n := by rw [← h, ← hsdef]; norm_num
    have h2 : (n : ℝ) < -2 := by rw [← h, ← hsdef]; norm_num
    have h1' : -3 < n := by exact_mod_cast h1
    have h2' : n < -2 := by exact_mod_cast h2
    omega
  have hp : NotPole s := notPole_of_not_int hint
  have hG := gamma_upper (s + 4) (by rw [← hsdef]; norm_num) (by rw [← hsdef]; norm_num)
  have hG0 : 0 < Gamma (s + 4) := Gamma_pos_of_pos (by rw [← hsdef]; norm_num)
  have hP : 9996 / 10000 ≤ |∏ j ∈ range 4, (s + j)| := by
    rw [le_abs, ← hsdef]
    norm_num [prod_range_succ]
  have hc : 1 - 2274 / 10000 * (s + 4 - 1) ≤ 912 / 1000 * (9996 / 10000) := by
    rw [← hsdef]; norm_num
  have hP0 : 0 < |∏ j ∈ range 4, (s + j)| := lt_of_lt_of_le (by norm_num) hP
  have h4 : Gamma s = Gamma (s + 4) / ∏ j ∈ range 4, (s + j) := by
    rw [gamma_eq_div hp 4]
    norm_num
  have hA : |Gamma s| ≤ 912 / 1000 := by
    rw [h4, abs_div, abs_of_pos hG0, div_le_iff₀ hP0]
    linarith
  have hA0 : 0 < |Gamma s| := by
    rw [h4, abs_div, abs_of_pos hG0]
    exact div_pos hG0 hP0
  unfold lgamma
  rw [← Real.log_abs]
  have := Real.log_le_sub_one_of_pos hA0
  rw [abs_of_neg (by linarith)]
  linarith

/-- **From 1/4 to 3/4**: `Γ x = Γ (x + 1)/x ≥ 0.8275/0.75`, so `log Γ x ≥ 1/20`. -/
theorem pos_quarter (x : ℝ) (h1 : 1 / 4 < x) (h2 : x < 3 / 4) : 1 / 20 ≤ |lgamma x| := by
  have hG := gamma_lower_mid (x + 1) (by linarith) (by linarith)
  have hx : Gamma x = Gamma (x + 1) / x := by
    rw [Gamma_add_one (by linarith)]
    field_simp
  have hA : 11 / 10 ≤ Gamma x := by
    rw [hx, le_div_iff₀ (by linarith)]
    nlinarith
  unfold lgamma
  have := log_ge_of_ge' (Gamma x) hA
  rw [abs_of_pos (by linarith)]
  linarith

/-- **From 5/4 to 7/4**: `Γ ≤ 0.9432` by the chords, so `log Γ x ≤ -1/20`. -/
theorem pos_mid (x : ℝ) (h1 : 5 / 4 < x) (h2 : x < 7 / 4) : 1 / 20 ≤ |lgamma x| := by
  have hA : Gamma x ≤ 9432 / 10000 := by
    rcases le_or_gt x (3 / 2) with h | h
    · have := gamma_upper x (by linarith) h
      linarith
    · have := gamma_upper2 x h.le (by linarith)
      linarith
  have hA0 : 0 < Gamma x := Gamma_pos_of_pos (by linarith)
  unfold lgamma
  have := Real.log_le_sub_one_of_pos hA0
  rw [abs_of_neg (by linarith)]
  linarith

/-- **From 9/4 on**: `log Γ` lies above the line through `3/2` and `2`, of slope at least
`0.2274`, so `log Γ x ≥ 1/20`. -/
theorem pos_large (x : ℝ) (h1 : 9 / 4 ≤ x) : 1 / 20 ≤ |lgamma x| := by
  obtain ⟨-, g2⟩ := gamma_three_halves_bounds
  have hl : Real.log (Gamma (3 / 2)) ≤ -(1137 / 10000) := by
    have := Real.log_le_sub_one_of_pos (Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2))
    linarith
  have hs := convexOn_log_Gamma.secant_mono (a := 2) (x := 3 / 2) (y := x)
    (by rw [Set.mem_Ioi]; norm_num) (by rw [Set.mem_Ioi]; norm_num)
    (by rw [Set.mem_Ioi]; linarith) (by norm_num) (by linarith) (by linarith)
  simp only [Function.comp_apply] at hs
  rw [Gamma_two, Real.log_one, show (3 / 2 : ℝ) - 2 = -(1 / 2) by norm_num] at hs
  have hpos : 0 < x - 2 := by linarith
  rw [le_div_iff₀ hpos] at hs
  have : (Real.log (Gamma (3 / 2)) - 0) / -(1 / 2) * (x - 2) =
      -(2 * Real.log (Gamma (3 / 2)) * (x - 2)) := by ring
  have hL : 1 / 20 ≤ lgamma x := by
    unfold lgamma
    nlinarith [mul_le_mul_of_nonneg_right hl hpos.le]
  rw [abs_of_pos (by linarith)]
  exact hL

end Verified.Examples.LgammaAccLower
