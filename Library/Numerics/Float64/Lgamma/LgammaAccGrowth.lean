import Library.Numerics.Float64.Lgamma.LgammaAccLower
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Lower bounds on `log Γ y` that turn the absolute part `y ε` of the error of
`LgammaAsymAcc.asym_spec` into a part relative to `log Γ y`: `log Γ y ≥ y/8` from `15/4`
(`growth_small`) and `log Γ y ≥ 13 y/10` from `23/2` (`growth_large`).  Both follow from the
convexity of `log Γ` (`Real.convexOn_log_Gamma`): past `y0`, `log Γ` lies above the line through
`y0 - 1` and `y0`, whose slope is `log (y0 - 1)`.  `lgamma_upper` bounds `log Γ y` by `2^812` up
to `2^802`, for the bounds on the high parts that the reflection and the renormalization need.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccGrowth
open Real LeanExe.ProofKit GammaBasic Finset

/-- Past `y0 ≥ 2`, `log Γ` lies above its secant through `y0 - 1` and `y0`. -/
theorem above_secant (y0 y : ℝ) (h0 : 2 ≤ y0) (hy : y0 ≤ y) :
    GammaBasic.lgamma y0 + Real.log (y0 - 1) * (y - y0) ≤ GammaBasic.lgamma y := by
  rcases hy.lt_or_eq with hlt | heq
  · have hc := convexOn_log_Gamma.secant_mono (a := y0) (x := y0 - 1) (y := y)
      (by rw [Set.mem_Ioi]; linarith) (by rw [Set.mem_Ioi]; linarith)
      (by rw [Set.mem_Ioi]; linarith) (ne_of_lt (by linarith)) hlt.ne' (by linarith)
    simp only [Function.comp_apply] at hc
    have hrec : Real.log (Gamma y0) = Real.log (Gamma (y0 - 1)) + Real.log (y0 - 1) := by
      have h := lgamma_add_one (x := y0 - 1) (notPole_of_neg_one_lt (by linarith) (by linarith))
      rw [show y0 - 1 + 1 = y0 by ring] at h
      exact h
    rw [show y0 - 1 - y0 = -1 by ring, hrec] at hc
    have hpos : 0 < y - y0 := by linarith
    rw [le_div_iff₀ hpos] at hc
    unfold GammaBasic.lgamma
    have : (Real.log (Gamma (y0 - 1)) - (Real.log (Gamma (y0 - 1)) + Real.log (y0 - 1))) / -1 =
        Real.log (y0 - 1) := by ring
    rw [this] at hc
    linarith
  · rw [heq, sub_self, mul_zero, add_zero]

/-- **`log Γ y ≥ y/8` from `15/4`.** -/
theorem growth_small (y : ℝ) (hy : 15 / 4 ≤ y) : y / 8 ≤ GammaBasic.lgamma y := by
  have hs := above_secant (15 / 4) y (by norm_num) hy
  have hG : 15 / 32 ≤ GammaBasic.lgamma (15 / 4) := by
    have hΓ : Gamma (15 / 4) = Gamma (7 / 4) * (77 / 16) := by
      rw [show (15 / 4 : ℝ) = 7 / 4 + ((2 : ℕ) : ℝ) by norm_num,
        gamma_add_nat (notPole_of_neg_one_lt (by norm_num) (by norm_num)) 2]
      norm_num [prod_range_succ]
    have hL := LgammaAccLower.gamma_lower (7 / 4) (by norm_num) (by norm_num)
    have hge : 3 ≤ Gamma (15 / 4) := by rw [hΓ]; linarith
    unfold GammaBasic.lgamma
    have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < Gamma (15 / 4))
    have : (Gamma (15 / 4))⁻¹ ≤ 1 / 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      norm_num
      linarith
    linarith
  have hl : 1 / 2 ≤ Real.log (15 / 4 - 1) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 15 / 4 - 1)
    norm_num at this ⊢
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hl (by linarith : (0 : ℝ) ≤ y - 15 / 4)]

/-- **`log Γ y ≥ 13 y/10` from `23/2`.** -/
theorem growth_large (y : ℝ) (hy : 23 / 2 ≤ y) : 13 * y / 10 ≤ GammaBasic.lgamma y := by
  have hs := above_secant (23 / 2) y (by norm_num) hy
  have hG : 16 ≤ GammaBasic.lgamma (23 / 2) := by
    have hΓ : Gamma (23 / 2) = Gamma (3 / 2) * ∏ j ∈ range 10, (3 / 2 + (j : ℝ)) := by
      rw [show (23 / 2 : ℝ) = 3 / 2 + ((10 : ℕ) : ℝ) by norm_num]
      exact gamma_add_nat (notPole_of_neg_one_lt (by norm_num) (by norm_num)) 10
    have hP : (13427000 : ℝ) ≤ ∏ j ∈ range 10, (3 / 2 + (j : ℝ)) := by
      norm_num [prod_range_succ]
    obtain ⟨g1, -⟩ := LgammaAccLower.gamma_three_halves_bounds
    have hge : 11800000 ≤ Gamma (23 / 2) := by
      rw [hΓ]
      nlinarith [mul_le_mul g1 hP (by norm_num) (by linarith)]
    have he : Real.exp 16 ≤ 11800000 := by
      have h1 := Real.exp_one_lt_d9
      have h16 : Real.exp 16 = Real.exp 1 ^ 16 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h16]
      calc Real.exp 1 ^ 16 ≤ (2.7182818286 : ℝ) ^ 16 :=
            pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 16
        _ ≤ 11800000 := by norm_num
    unfold GammaBasic.lgamma
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hl : 2 ≤ Real.log (23 / 2 - 1) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    have := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 2
    norm_num at this ⊢
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hl (by linarith : (0 : ℝ) ≤ y - 23 / 2)]

/-- **`log Γ y ≤ 2^812` up to `2^802`**: `Γ` increases from 2, and `Γ N = (N - 1)! ≤ N^N` at
`N = 2^802`. -/
theorem lgamma_upper (y : ℝ) (h1 : 2 ≤ y) (h2 : y ≤ 2 ^ 802) : GammaBasic.lgamma y ≤ 2 ^ 812 := by
  set N : ℕ := 2 ^ 802 with hN
  have hNr : (N : ℝ) = 2 ^ 802 := by rw [hN]; push_cast; rfl
  have hm := Gamma_strictMonoOn_Ici.monotoneOn (show y ∈ Set.Ici 2 by rw [Set.mem_Ici]; exact h1)
    (show (N : ℝ) ∈ Set.Ici 2 by rw [Set.mem_Ici, hNr]; exact le_self_pow₀ (by norm_num) (by norm_num))
    (by rw [hNr]; exact h2)
  have h1N : 1 ≤ N := by rw [hN]; exact Nat.one_le_two_pow
  have hG : Gamma (N : ℝ) = ((N - 1).factorial : ℝ) := by
    have : (N : ℝ) = ((N - 1 : ℕ) : ℝ) + 1 := by
      push_cast [Nat.cast_sub h1N]
      ring
    rw [this, Gamma_nat_eq_factorial]
  have hf : ((N - 1).factorial : ℝ) ≤ (N : ℝ) ^ N := by
    have h := Nat.factorial_le_pow (N - 1)
    have h3 : (N - 1) ^ (N - 1) ≤ N ^ N :=
      le_trans (Nat.pow_le_pow_left (Nat.sub_le N 1) _)
        (Nat.pow_le_pow_right (by omega) (Nat.sub_le N 1))
    exact_mod_cast h.trans h3
  have hGN : Gamma (N : ℝ) ≤ (N : ℝ) ^ N := by rw [hG]; exact hf
  have hpos : 0 < Gamma y := Gamma_pos_of_pos (by linarith)
  unfold GammaBasic.lgamma
  have hl := Real.log_le_log hpos (hm.trans hGN)
  rw [Real.log_pow, hNr, Real.log_pow] at hl
  have h2l := Real.log_two_lt_d9
  calc Real.log (Gamma y) ≤ 2 ^ 802 * (((802 : ℕ) : ℝ) * Real.log 2) := hl
    _ ≤ 2 ^ 802 * 1024 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        norm_num at h2l ⊢
        linarith
    _ = 2 ^ 812 := by
        rw [show (2 : ℝ) ^ 812 = 2 ^ 802 * 2 ^ 10 by rw [← pow_add],
          show (2 : ℝ) ^ 10 = 1024 by norm_num]

end Library.Numerics.Float64.Lgamma.LgammaAccGrowth
