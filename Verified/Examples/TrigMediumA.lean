import Verified.Examples.TrigMediumCases

/-!
The first outcome of the medium reduction: when the exponent of `y0 = R1 - W1` is at least that of
`x` minus 16, `y0` and `(R1 - y0) - W1` form an exact two-sum of `R1 - W1`, within `x / 2 ^ 84` of
`r = x - N π/2`, and `|r| > x / 2 ^ 19`.
-/

namespace Verified.Examples.TrigMediumA

open CodeLib.IEEE64 LeanExe.ProofKit TrigFloatTools TrigNearest TrigSmall TrigMediumConst
  TrigMediumCases

theorem caseA (X F : UInt64) (N : Nat) (h : Med X F N)
    (hstop : Wasm.IEEE64.exponent X ≤ Wasm.IEEE64.exponent (Y0 X F) + 16) :
    Finite (Y0 X F) ∧ Finite (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R1 X F) (Y0 X F)) (W1 F)) ∧
      |value (Y0 X F) + value (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R1 X F) (Y0 X F)) (W1 F)) -
          (value X - N * (Real.pi / 2))| ≤ |value X - N * (Real.pi / 2)| / 2 ^ 60 ∧
      |value (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R1 X F) (Y0 X F)) (W1 F))| ≤
        |value (Y0 X F)| / 2 ^ 52 := by
  obtain ⟨hrl, hru, hNle, hE1, hE2, hRf, hRv, hRd, hWf, hWe, hD⟩ := med_common X F N h
  obtain ⟨-, -, -, hP1tl, hP1tu, -, -, -, -⟩ := pio2_values
  have hx1 := h.x1
  have hx0 : 0 < value X := by linarith
  have hpi4 : Real.pi < 3.15 := Real.pi_lt_d2
  have hY := exp_lower (Y0 X F) X 16 (by omega) hstop
  rw [abs_of_pos hx0] at hY
  have hP1t0 : 0 ≤ value pio2_1t := le_trans (by norm_num) hP1tl
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  set D := value (R1 X F) - value (W1 F) with hDdef
  set r := value X - N * (Real.pi / 2) with hrdef
  -- `W1` is small.
  have hW : |value (W1 F)| ≤ value X / 2 ^ 32 := by
    have h1 : |value (W1 F)| ≤ N * value pio2_1t + N * value pio2_1t / 2 ^ 52 := by
      have := abs_sub_abs_le_abs_sub (value (W1 F)) (N * value pio2_1t)
      rw [abs_of_nonneg (mul_nonneg hN0 hP1t0)] at this
      linarith
    have h2 : (N : ℝ) * value pio2_1t ≤ 6 / 5 * value X * (1 / 2 ^ 33) :=
      mul_le_mul hNle hP1tu hP1t0 (by linarith)
    have h3 : 6 / 5 * value X * (1 / 2 ^ 33) + 6 / 5 * value X * (1 / 2 ^ 33) / 2 ^ 52 ≤
        value X / 2 ^ 32 := by
      have e : 6 / 5 * value X * (1 / 2 ^ 33) + 6 / 5 * value X * (1 / 2 ^ 33) / 2 ^ 52 =
          value X * (6 / 5 / 2 ^ 33 * (1 + 1 / 2 ^ 52)) := by ring
      rw [e, div_eq_mul_one_div (value X)]
      exact mul_le_mul_of_nonneg_left (by norm_num) hx0.le
    have h4 : (N : ℝ) * value pio2_1t / 2 ^ 52 ≤ 6 / 5 * value X * (1 / 2 ^ 33) / 2 ^ 52 :=
      div_le_div_of_nonneg_right h2 (by norm_num)
    linarith
  have hDr : |D - r| ≤ value X / 2 ^ 84 := hD
  have hDu : |D| ≤ 1 := by
    have := abs_add_le r (D - r)
    rw [show r + (D - r) = D by ring] at this
    have : value X / 2 ^ 84 ≤ 2 ^ 21 / 2 ^ 84 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have := h.x2
      have h2pi : 0.6 ≤ 2 / Real.pi := by
        rw [le_div_iff₀ (by linarith [Real.pi_gt_three])]
        linarith
      nlinarith
    have : (2 : ℝ) ^ 21 / 2 ^ 84 ≤ 1 / 100 := by norm_num
    linarith
  obtain ⟨-, hYe⟩ := sub_rel (R1 X F) (W1 F) hRf hWf (by
    rw [← hDdef]
    exact lt_of_le_of_lt hDu (one_lt_pow₀ (by norm_num) (by norm_num)))
  rw [← hDdef] at hYe
  have hYD : |value (Y0 X F)| ≤ |D| + |D| / 2 ^ 53 := by
    have := abs_sub_abs_le_abs_sub (value (Y0 X F)) D
    unfold Y0 at this ⊢
    linarith
  have hDlo : value X / 2 ^ 18 ≤ |D| := by
    have h1 : value X / 2 ^ 17 < |D| * (1 + 1 / 2 ^ 53) := by
      have : |D| + |D| / 2 ^ 53 = |D| * (1 + 1 / 2 ^ 53) := by ring
      linarith
    have h2 : |D| * (1 + 1 / 2 ^ 53) ≤ |D| * 2 := mul_le_mul_of_nonneg_left (by norm_num)
      (abs_nonneg _)
    have e : value X / 2 ^ 18 * 2 = value X / 2 ^ 17 := by ring
    linarith
  have hR1 : 4 * |value (W1 F)| ≤ |value (R1 X F)| := by
    have := abs_sub_abs_le_abs_sub (value (R1 X F)) (value (W1 F))
    have h5 : 5 * (value X / 2 ^ 32) ≤ value X / 2 ^ 18 := by
      rw [div_eq_mul_one_div (value X), div_eq_mul_one_div (value X)]
      nlinarith
    rw [← hDdef] at this
    have := abs_sub_abs_le_abs_sub D (-value (W1 F))
    rw [show D - -value (W1 F) = value (R1 X F) by rw [hDdef]; ring, abs_neg] at this
    linarith
  have hRbig : |value (R1 X F)| < 2 ^ 1020 := by
    have := abs_add_le D (value (W1 F))
    rw [show D + value (W1 F) = value (R1 X F) by rw [hDdef]; ring] at this
    have : value X / 2 ^ 32 ≤ 1 := by
      rw [div_le_one (by norm_num)]
      have := h.x2
      have h2pi : 0.6 ≤ 2 / Real.pi := by
        rw [le_div_iff₀ (by linarith [Real.pi_gt_three])]
        linarith
      nlinarith
    have h2 : |value (R1 X F)| ≤ 2 := by linarith
    exact lt_of_le_of_lt h2 (lt_of_lt_of_le (by norm_num : (2 : ℝ) < 2 ^ 2)
      (pow_le_pow_right₀ (by norm_num) (by norm_num)))
  obtain ⟨hYf, -, hdf, hdv, hef, hev⟩ := small_two_diff (R1 X F) (W1 F) hRf hWf hR1 hRbig
  have hY0 : Y0 X F = Wasm.IEEE64.sub (R1 X F) (W1 F) := rfl
  rw [hY0]
  refine ⟨hYf, hef, ?_, ?_⟩
  · rw [hev, show value (Wasm.IEEE64.sub (R1 X F) (W1 F)) +
      (value (R1 X F) - value (W1 F) - value (Wasm.IEEE64.sub (R1 X F) (W1 F))) - r = D - r by
        rw [hDdef]; ring]
    have hrlo : value X / 2 ^ 19 ≤ |r| := by
      have := abs_sub_abs_le_abs_sub D (D - r)
      rw [show D - (D - r) = r by ring] at this
      have : value X / 2 ^ 84 ≤ value X / 2 ^ 19 := by
        apply div_le_div_of_nonneg_left hx0.le (by norm_num) (by norm_num)
      have e : value X / 2 ^ 18 = value X / 2 ^ 19 + value X / 2 ^ 19 := by ring
      linarith
    calc |D - r| ≤ value X / 2 ^ 84 := hDr
      _ = value X / 2 ^ 19 / 2 ^ 65 := by ring
      _ ≤ |r| / 2 ^ 65 := div_le_div_of_nonneg_right hrlo (by norm_num)
      _ ≤ |r| / 2 ^ 60 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
  · rw [hev, show value (R1 X F) - value (W1 F) - value (Wasm.IEEE64.sub (R1 X F) (W1 F)) =
      -(value (Wasm.IEEE64.sub (R1 X F) (W1 F)) - D) by rw [hDdef]; ring, abs_neg]
    unfold Y0 at hYD
    have h1 : |D| ≤ |value (Wasm.IEEE64.sub (R1 X F) (W1 F))| + |D| / 2 ^ 53 := by
      have := abs_sub_abs_le_abs_sub D (value (Wasm.IEEE64.sub (R1 X F) (W1 F)))
      rw [abs_sub_comm D] at this
      linarith
    have hn := abs_nonneg D
    have h2 : |D| / 2 ^ 53 ≤ |D| / 2 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
    have h3 : |D| ≤ 2 * |value (Wasm.IEEE64.sub (R1 X F) (W1 F))| := by linarith
    have h4 : |D| / 2 ^ 53 ≤ 2 * |value (Wasm.IEEE64.sub (R1 X F) (W1 F))| / 2 ^ 53 :=
      div_le_div_of_nonneg_right h3 (by norm_num)
    have h5 : 2 * |value (Wasm.IEEE64.sub (R1 X F) (W1 F))| / 2 ^ 53 =
        |value (Wasm.IEEE64.sub (R1 X F) (W1 F))| / 2 ^ 52 := by ring
    linarith

#print axioms caseA

end Verified.Examples.TrigMediumA
