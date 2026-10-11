import Verified.Examples.TrigMediumCases

/-!
The second outcome of the medium reduction: when the first step cancels below `x / 2 ^ 16` and
the second stops, `y0 + y1 = R2 - W2'`, within `x / 2 ^ 118` of `r = x - N π/2`, and
`|r| > x / 2 ^ 52`.
-/

namespace Verified.Examples.TrigMediumB

open CodeLib.IEEE64 LeanExe.ProofKit TrigFloatTools TrigNearest TrigSmall TrigMediumConst
  TrigMediumCases

/-- The second step of the medium reduction, after the first cancels below `x / 2 ^ 16`:
`W2 = N pio2_2` exact, `R2 = R1 - W2` rounded on the grid of `2 ^ -65`, and `R2 - W2'` within
`x / 2 ^ 118` of `r`. -/
theorem step2 (X F : UInt64) (N : Nat) (h : Med X F N)
    (hgo : Wasm.IEEE64.exponent (Y0 X F) + 16 < Wasm.IEEE64.exponent X) :
    Finite (W2 F) ∧ value (W2 F) = N * value pio2_2 ∧
      (2 : Int) ^ 1009 ∣ Wasm.IEEE64.scaledValue (W2 F) ∧
      Finite (R2 X F) ∧ (2 : Int) ^ 1009 ∣ Wasm.IEEE64.scaledValue (R2 X F) ∧
      |value (R2 X F) - (value (R1 X F) - value (W2 F))| ≤ value X / 2 ^ 67 ∧
      Finite (W2' X F) ∧ |value (W2' X F)| ≤ value X / 2 ^ 65 ∧
      |value (R2 X F) - value (W2' X F) - (value X - N * (Real.pi / 2))| ≤ value X / 2 ^ 118 := by
  obtain ⟨hrl, hru, hNle, hE1, hE2, hRf, hRv, hRd, hWf, hWe, hD⟩ := med_common X F N h
  obtain ⟨-, hP2, -, hP1tl, hP1tu, hP2tl, hP2tu, -, -⟩ := pio2_values
  obtain ⟨-, -, hP2f, hP2tf, -, -, -, hs2, -, -, -, -, -, -, -⟩ := consts_checked
  have hp1 := pio2_close
  have hp2 := pio2_2_close
  rw [abs_le] at hp1 hp2
  have hx1 := h.x1
  have hx0 : 0 < value X := by linarith
  have hx21 : value X ≤ 2 ^ 21 := by
    have h2pi : 0.6 ≤ 2 / Real.pi := by
      rw [le_div_iff₀ (by linarith [Real.pi_gt_three])]
      linarith [Real.pi_lt_d2]
    have h6 : value X * 0.6 ≤ 2 ^ 20 := le_trans (mul_le_mul_of_nonneg_left h2pi hx0.le) h.x2
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hN2 : (N : ℝ) ≤ 2 ^ 20 := by exact_mod_cast h.N2
  have hP1t0 : 0 ≤ value pio2_1t := le_trans (by norm_num) hP1tl
  have hP2t0 : 0 ≤ value pio2_2t := le_trans (by norm_num) hP2tl
  set r := value X - N * (Real.pi / 2) with hrdef
  set D := value (R1 X F) - value (W1 F) with hDdef
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 3.15 := Real.pi_lt_d2
  have hFv : value F = N := by
    rw [TrigSmall.value_of_scaled, h.Fv]
    push_cast
    rw [mul_div_assoc, div_self (pow_ne_zero _ (by norm_num)), mul_one]
  -- The first step cancelled below `x / 2 ^ 16`.
  have hY := exp_upper (Y0 X F) X 16 (by omega) hgo
  rw [abs_of_pos hx0] at hY
  have hDu1 : |D| ≤ 1 := by
    have := abs_add_le r (D - r)
    rw [show r + (D - r) = D by ring] at this
    have h1 : value X / 2 ^ 84 ≤ 2 ^ 21 / 2 ^ 84 := div_le_div_of_nonneg_right hx21 (by norm_num)
    have : (2 : ℝ) ^ 21 / 2 ^ 84 ≤ 1 / 100 := by norm_num
    have := hD
    linarith
  obtain ⟨-, hYe⟩ := sub_rel (R1 X F) (W1 F) hRf hWf
    (lt_of_le_of_lt hDu1 (one_lt_pow₀ (by norm_num) (by norm_num)))
  have hY0 : Y0 X F = Wasm.IEEE64.sub (R1 X F) (W1 F) := rfl
  rw [hY0] at hY
  rw [← hDdef] at hYe
  have hDs : |D| ≤ value X / 2 ^ 15 := by
    have h1 : |D| ≤ |value (Wasm.IEEE64.sub (R1 X F) (W1 F))| + |D| / 2 ^ 53 := by
      have := abs_sub_abs_le_abs_sub D (value (Wasm.IEEE64.sub (R1 X F) (W1 F)))
      rw [abs_sub_comm D] at this
      linarith
    have h2 : |D| / 2 ^ 53 ≤ |D| / 2 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
      (by norm_num)
    have e : value X / 2 ^ 15 = 2 * (value X / 2 ^ 16) := by ring
    linarith
  -- `W2 = N · pio2_2`, exact.
  obtain ⟨hW2f, hW2s⟩ := mul_count F pio2_2 N 2242054355 1009 h.Ff hP2f h.Fv h.N1 h.N2 hs2
    (by norm_num) (by norm_num) (by norm_num)
  have hW2v : value (W2 F) = N * value pio2_2 := by
    rw [W2, TrigSmall.value_of_scaled, hW2s, hP2]
    push_cast
    rw [show (1074 : Nat) = 1009 + 65 by norm_num, pow_add]
    field_simp
  have hW2d : (2 : Int) ^ 1009 ∣ Wasm.IEEE64.scaledValue (W2 F) := by
    rw [W2, hW2s]
    exact Dvd.intro_left _ rfl
  -- `A2 ≈ N · pio2_2t`.
  have hNt : |value F * value pio2_2t| = N * value pio2_2t := by
    rw [hFv, abs_of_nonneg (mul_nonneg hN0 hP2t0)]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.N1
  obtain ⟨hA2f, hA2e⟩ := mul_rel F pio2_2t h.Ff hP2tf (by
      rw [hNt]
      have h900 : (1 : ℝ) / 2 ^ 900 ≤ 1 / 2 ^ 69 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
      calc (1 : ℝ) / 2 ^ 900 ≤ 1 * (1 / 2 ^ 69) := by rw [one_mul]; exact h900
        _ ≤ N * value pio2_2t := mul_le_mul hN1 hP2tl (by norm_num) hN0)
    (by
      rw [hNt]
      calc (N : ℝ) * value pio2_2t ≤ 2 ^ 20 * (1 / 2 ^ 68) := mul_le_mul hN2 hP2tu hP2t0 (by norm_num)
        _ ≤ 2 ^ 100 := by norm_num)
  rw [hNt, hFv] at hA2e
  replace hA2e : |value (A2 F) - N * value pio2_2t| ≤ N * value pio2_2t / 2 ^ 52 := hA2e
  replace hA2f : Finite (A2 F) := hA2f
  have hA2 : |value (A2 F)| ≤ value X / 2 ^ 67 := by
    have h1 : (N : ℝ) * value pio2_2t ≤ 6 / 5 * value X * (1 / 2 ^ 68) :=
      mul_le_mul hNle hP2tu hP2t0 (by linarith)
    have h2 : |value (A2 F)| ≤ N * value pio2_2t + N * value pio2_2t / 2 ^ 52 := by
      have := abs_sub_abs_le_abs_sub (value (A2 F)) (N * value pio2_2t)
      rw [abs_of_nonneg (mul_nonneg hN0 hP2t0)] at this
      linarith
    have h3 : (N : ℝ) * value pio2_2t / 2 ^ 52 ≤ 6 / 5 * value X * (1 / 2 ^ 68) / 2 ^ 52 :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have e : value X / 2 ^ 67 = value X * (1 / 2 ^ 67) := by ring
    have e2 : 6 / 5 * value X * (1 / 2 ^ 68) + 6 / 5 * value X * (1 / 2 ^ 68) / 2 ^ 52 =
        value X * (6 / 5 / 2 ^ 68 * (1 + 1 / 2 ^ 52)) := by ring
    have h4 : value X * (6 / 5 / 2 ^ 68 * (1 + 1 / 2 ^ 52)) ≤ value X * (1 / 2 ^ 67) :=
      mul_le_mul_of_nonneg_left (by norm_num) hx0.le
    linarith
  -- The bound `B` of `R1 - W2`.
  have hP12 : |value pio2_1t - value pio2_2| ≤ 1 / 2 ^ 67 := by
    rw [abs_le]
    constructor <;> linarith
  have hW12 : |value (W1 F) - value (W2 F)| ≤ value X / 2 ^ 66 := by
    rw [hW2v, show value (W1 F) - N * value pio2_2 =
      (value (W1 F) - N * value pio2_1t) + N * (value pio2_1t - value pio2_2) by ring]
    have h1 := abs_add_le (value (W1 F) - N * value pio2_1t) (N * (value pio2_1t - value pio2_2))
    have h2 : |(N : ℝ) * (value pio2_1t - value pio2_2)| ≤ N * (1 / 2 ^ 67) := by
      rw [abs_mul, abs_of_nonneg hN0]
      exact mul_le_mul_of_nonneg_left hP12 hN0
    have h3 : (N : ℝ) * value pio2_1t / 2 ^ 52 ≤ N * (1 / 2 ^ 33) / 2 ^ 52 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hP1tu hN0) (by norm_num)
    have h4 : (N : ℝ) * (1 / 2 ^ 33) / 2 ^ 52 + N * (1 / 2 ^ 67) ≤ value X / 2 ^ 66 := by
      have e : (N : ℝ) * (1 / 2 ^ 33) / 2 ^ 52 + N * (1 / 2 ^ 67) = N * (1 / 2 ^ 85 + 1 / 2 ^ 67) :=
        by ring
      rw [e]
      have h5 : (N : ℝ) * (1 / 2 ^ 85 + 1 / 2 ^ 67) ≤ 6 / 5 * value X * (1 / 2 ^ 85 + 1 / 2 ^ 67) :=
        mul_le_mul_of_nonneg_right hNle (by norm_num)
      have e2 : 6 / 5 * value X * (1 / 2 ^ 85 + 1 / 2 ^ 67) =
          value X * (6 / 5 * (1 / 2 ^ 85 + 1 / 2 ^ 67)) := by ring
      have e3 : value X / 2 ^ 66 = value X * (1 / 2 ^ 66) := by ring
      have h6 : value X * (6 / 5 * (1 / 2 ^ 85 + 1 / 2 ^ 67)) ≤ value X * (1 / 2 ^ 66) :=
        mul_le_mul_of_nonneg_left (by norm_num) hx0.le
      linarith
    linarith
  have hB : |value (R1 X F) - value (W2 F)| ≤ value X / 2 ^ 14 := by
    have := abs_add_le D (value (W1 F) - value (W2 F))
    rw [show D + (value (W1 F) - value (W2 F)) = value (R1 X F) - value (W2 F) by
      rw [hDdef]; ring] at this
    have e : value X / 2 ^ 14 = value X / 2 ^ 15 + value X / 2 ^ 15 := by ring
    have : value X / 2 ^ 66 ≤ value X / 2 ^ 15 :=
      div_le_div_of_nonneg_left hx0.le (by norm_num) (by norm_num)
    linarith
  have hB7 : value X / 2 ^ 14 ≤ 2 ^ 7 := by
    rw [div_le_iff₀ (by norm_num)]
    calc value X ≤ 2 ^ 21 := hx21
      _ = 2 ^ 7 * 2 ^ 14 := by norm_num
  have hB2 : value X / 2 ^ 14 < 2 ^ 1000 :=
    lt_of_le_of_lt hB7 (pow_lt_pow_right₀ (by norm_num) (by norm_num))
  have hfit : |value (W2 F)| + value X / 2 ^ 14 / 2 ^ 53 ≤ (2 : ℝ) ^ (53 + 1009) / 2 ^ 1074 := by
    have e : (2 : ℝ) ^ (53 + 1009) / 2 ^ 1074 = 1 / 2 ^ 12 := by
      rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
    rw [e, hW2v, abs_of_nonneg (mul_nonneg hN0 (by rw [hP2]; positivity)), hP2]
    have h1 : (N : ℝ) * (2242054355 / 2 ^ 65) ≤ 2 ^ 20 * (2242054355 / 2 ^ 65) :=
      mul_le_mul_of_nonneg_right hN2 (by positivity)
    have h2 : value X / 2 ^ 14 / 2 ^ 53 ≤ 2 ^ 7 / 2 ^ 53 := div_le_div_of_nonneg_right hB7
      (by norm_num)
    have : (2 : ℝ) ^ 20 * (2242054355 / 2 ^ 65) + 2 ^ 7 / 2 ^ 53 ≤ 1 / 2 ^ 12 := by norm_num
    linarith
  have hAe : |value (A2 F)| + value X / 2 ^ 14 / 2 ^ 53 < 2 ^ 1000 := by
    have h1 : value X / 2 ^ 67 ≤ 2 ^ 21 / 2 ^ 67 := div_le_div_of_nonneg_right hx21 (by norm_num)
    have h2 : value X / 2 ^ 14 / 2 ^ 53 ≤ 2 ^ 7 / 2 ^ 53 := div_le_div_of_nonneg_right hB7
      (by norm_num)
    have h3 : |value (A2 F)| + value X / 2 ^ 14 / 2 ^ 53 ≤ 1 := by
      have : (2 : ℝ) ^ 21 / 2 ^ 67 + 2 ^ 7 / 2 ^ 53 ≤ 1 := by norm_num
      linarith
    exact lt_of_le_of_lt h3 (one_lt_pow₀ (by norm_num) (by norm_num))
  obtain ⟨hR2f, hR2d, hR2e, hE2f, hE2v, hW2'f, hW2'e⟩ := comp_step (R1 X F) (W2 F) (A2 F) 1009
    (by norm_num) hRf hW2f hA2f hRd hW2d (value X / 2 ^ 14) hB hB2 hfit hAe
  have hR2 : R2 X F = Wasm.IEEE64.sub (R1 X F) (W2 F) := rfl
  have hW2' : W2' X F = Wasm.IEEE64.sub (A2 F)
      (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R1 X F) (R2 X F)) (W2 F)) := rfl
  rw [← hR2] at hR2f hR2d hR2e hE2f hE2v hW2'f hW2'e
  rw [← hW2'] at hW2'f hW2'e
  set E2 := value (R1 X F) - value (W2 F) - value (R2 X F) with hE2def
  -- The second difference `D2 = R2 - W2'`.
  set D2 := value (R2 X F) - value (W2' X F) with hD2def
  have hB53 : value X / 2 ^ 14 / 2 ^ 53 = value X / 2 ^ 67 := by ring
  rw [hB53] at hR2e hW2'e
  have hE2 : |E2| ≤ value X / 2 ^ 67 := by
    rw [hE2def, show value (R1 X F) - value (W2 F) - value (R2 X F) =
      -(value (R2 X F) - (value (R1 X F) - value (W2 F))) by ring, abs_neg]
    exact hR2e
  have hdel : |value (W2' X F) - (value (A2 F) - E2)| ≤ (value X / 2 ^ 67 + value X / 2 ^ 67) / 2 ^ 53 :=
    hW2'e.trans (div_le_div_of_nonneg_right (by linarith) (by norm_num))
  have hD2r : |D2 - r| ≤ value X / 2 ^ 118 := by
    have e : D2 - r = (N * (Real.pi / 2 - value pio2_1 - value pio2_2 - value pio2_2t)) -
        (value (A2 F) - N * value pio2_2t) - (value (W2' X F) - (value (A2 F) - E2)) := by
      rw [hD2def, hrdef, hE2def, hRv, hW2v]
      ring
    rw [e]
    have h1 : |(N : ℝ) * (Real.pi / 2 - value pio2_1 - value pio2_2 - value pio2_2t)| ≤
        N * (1 / 2 ^ 121) := by
      rw [abs_mul, abs_of_nonneg hN0]
      apply mul_le_mul_of_nonneg_left _ hN0
      rw [abs_le]
      constructor <;> linarith
    have h2 : |value (A2 F) - N * value pio2_2t| ≤ N * (1 / 2 ^ 68) / 2 ^ 52 :=
      hA2e.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hP2tu hN0) (by norm_num))
    have h3 := abs_sub (N * (Real.pi / 2 - value pio2_1 - value pio2_2 - value pio2_2t))
      (value (A2 F) - N * value pio2_2t)
    have h4 := abs_sub (N * (Real.pi / 2 - value pio2_1 - value pio2_2 - value pio2_2t) -
      (value (A2 F) - N * value pio2_2t)) (value (W2' X F) - (value (A2 F) - E2))
    have h5 : (N : ℝ) * (1 / 2 ^ 121) + N * (1 / 2 ^ 68) / 2 ^ 52 +
        (value X / 2 ^ 67 + value X / 2 ^ 67) / 2 ^ 53 ≤ value X / 2 ^ 118 := by
      have e2 : (N : ℝ) * (1 / 2 ^ 121) + N * (1 / 2 ^ 68) / 2 ^ 52 = N * (3 / 2 ^ 121) := by ring
      rw [e2]
      have h6 : (N : ℝ) * (3 / 2 ^ 121) ≤ 6 / 5 * value X * (3 / 2 ^ 121) :=
        mul_le_mul_of_nonneg_right hNle (by norm_num)
      have e3 : 6 / 5 * value X * (3 / 2 ^ 121) + (value X / 2 ^ 67 + value X / 2 ^ 67) / 2 ^ 53 =
          value X * (18 / 5 / 2 ^ 121 + 2 / 2 ^ 120) := by ring
      have e4 : value X / 2 ^ 118 = value X * (1 / 2 ^ 118) := by ring
      have h7 : value X * (18 / 5 / 2 ^ 121 + 2 / 2 ^ 120) ≤ value X * (1 / 2 ^ 118) :=
        mul_le_mul_of_nonneg_left (by norm_num) hx0.le
      linarith
    linarith
  have hW2'b : |value (W2' X F)| ≤ value X / 2 ^ 65 := by
    have h1 := abs_sub_abs_le_abs_sub (value (W2' X F)) (value (A2 F) - E2)
    have h2 := abs_sub (value (A2 F)) E2
    have h3 : (value X / 2 ^ 67 + value X / 2 ^ 67) / 2 ^ 53 ≤ value X / 2 ^ 67 := by
      have e : (value X / 2 ^ 67 + value X / 2 ^ 67) / 2 ^ 53 = value X / 2 ^ 67 / 2 ^ 52 := by ring
      rw [e]
      exact div_le_self (by positivity) (by norm_num)
    have e : value X / 2 ^ 65 = 4 * (value X / 2 ^ 67) := by ring
    linarith
  exact ⟨hW2f, hW2v, hW2d, hR2f, hR2d, hR2e, hW2'f, hW2'b, hD2r⟩

theorem caseB (X F : UInt64) (N : Nat) (h : Med X F N)
    (hgo : Wasm.IEEE64.exponent (Y0 X F) + 16 < Wasm.IEEE64.exponent X)
    (hstop : Wasm.IEEE64.exponent X ≤ Wasm.IEEE64.exponent (Y0b X F) + 49) :
    Finite (Y0b X F) ∧ Finite (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R2 X F) (Y0b X F)) (W2' X F)) ∧
      |value (Y0b X F) + value (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R2 X F) (Y0b X F)) (W2' X F)) -
          (value X - N * (Real.pi / 2))| ≤ |value X - N * (Real.pi / 2)| / 2 ^ 60 ∧
      |value (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R2 X F) (Y0b X F)) (W2' X F))| ≤
        |value (Y0b X F)| / 2 ^ 52 := by
  obtain ⟨-, -, -, hR2f, -, -, hW2'f, hW2'b, hD2r⟩ := step2 X F N h hgo
  obtain ⟨hrl, hru, hNle, hE1, hE2, -, -, -, -, -, -⟩ := med_common X F N h
  have hpi4 : Real.pi < 3.15 := Real.pi_lt_d2
  have hx1 := h.x1
  have hx0 : 0 < value X := by linarith
  have hx21 : value X ≤ 2 ^ 21 := by
    have h2pi : 0.6 ≤ 2 / Real.pi := by
      rw [le_div_iff₀ (by linarith [Real.pi_gt_three])]
      linarith [Real.pi_lt_d2]
    have h6 : value X * 0.6 ≤ 2 ^ 20 := le_trans (mul_le_mul_of_nonneg_left h2pi hx0.le) h.x2
    linarith
  set r := value X - N * (Real.pi / 2) with hrdef
  set D2 := value (R2 X F) - value (W2' X F) with hD2def
  -- `y0` of the second step.
  have hD2u : |D2| ≤ 1 := by
    have := abs_add_le r (D2 - r)
    rw [show r + (D2 - r) = D2 by ring] at this
    have h1 : value X / 2 ^ 118 ≤ 2 ^ 21 / 2 ^ 118 := div_le_div_of_nonneg_right hx21 (by norm_num)
    have : (2 : ℝ) ^ 21 / 2 ^ 118 ≤ 1 / 100 := by norm_num
    linarith
  obtain ⟨-, hYbe⟩ := sub_rel (R2 X F) (W2' X F) hR2f hW2'f
    (lt_of_le_of_lt hD2u (one_lt_pow₀ (by norm_num) (by norm_num)))
  have hYb : Y0b X F = Wasm.IEEE64.sub (R2 X F) (W2' X F) := rfl
  rw [← hD2def, ← hYb] at hYbe
  have hYlo := exp_lower (Y0b X F) X 49 (by omega) hstop
  rw [abs_of_pos hx0] at hYlo
  have hD2lo : value X / 2 ^ 51 ≤ |D2| := by
    have h1 : |value (Y0b X F)| ≤ |D2| + |D2| / 2 ^ 53 := by
      have := abs_sub_abs_le_abs_sub (value (Y0b X F)) D2
      linarith
    have h2 : |D2| / 2 ^ 53 ≤ |D2| := div_le_self (abs_nonneg _) (by norm_num)
    have e : value X / 2 ^ 50 = 2 * (value X / 2 ^ 51) := by ring
    linarith
  have hR2W : 4 * |value (W2' X F)| ≤ |value (R2 X F)| := by
    have := abs_sub_abs_le_abs_sub D2 (-value (W2' X F))
    rw [show D2 - -value (W2' X F) = value (R2 X F) by rw [hD2def]; ring, abs_neg] at this
    have e : value X / 2 ^ 51 = 2 ^ 14 * (value X / 2 ^ 65) := by ring
    have h1 : (5 : ℝ) * (value X / 2 ^ 65) ≤ 2 ^ 14 * (value X / 2 ^ 65) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    linarith
  have hR2big : |value (R2 X F)| < 2 ^ 1020 := by
    have h1 := abs_add_le D2 (value (W2' X F))
    rw [show D2 + value (W2' X F) = value (R2 X F) by rw [hD2def]; ring] at h1
    have h2 : value X / 2 ^ 65 ≤ 1 := by
      rw [div_le_one (by norm_num)]
      calc value X ≤ 2 ^ 21 := hx21
        _ ≤ 2 ^ 65 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h3 : |value (R2 X F)| ≤ 2 := by linarith
    exact lt_of_le_of_lt h3 (lt_of_lt_of_le (by norm_num : (2 : ℝ) < 2 ^ 2)
      (pow_le_pow_right₀ (by norm_num) (by norm_num)))
  obtain ⟨hYbf, -, hdf, hdv, hef, hev⟩ := small_two_diff (R2 X F) (W2' X F) hR2f hW2'f hR2W hR2big
  rw [← hYb] at hYbf hdf hdv hef hev
  refine ⟨hYbf, hef, ?_, ?_⟩
  · rw [hev, show value (Y0b X F) + (value (R2 X F) - value (W2' X F) - value (Y0b X F)) - r =
      D2 - r by rw [hD2def]; ring]
    have hrlo : value X / 2 ^ 52 ≤ |r| := by
      have := abs_sub_abs_le_abs_sub D2 (D2 - r)
      rw [show D2 - (D2 - r) = r by ring] at this
      have : value X / 2 ^ 118 ≤ value X / 2 ^ 52 :=
        div_le_div_of_nonneg_left hx0.le (by norm_num) (by norm_num)
      have e : value X / 2 ^ 51 = value X / 2 ^ 52 + value X / 2 ^ 52 := by ring
      linarith
    calc |D2 - r| ≤ value X / 2 ^ 118 := hD2r
      _ = value X / 2 ^ 52 / 2 ^ 66 := by ring
      _ ≤ |r| / 2 ^ 66 := div_le_div_of_nonneg_right hrlo (by norm_num)
      _ ≤ |r| / 2 ^ 60 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
  · rw [hev, show value (R2 X F) - value (W2' X F) - value (Y0b X F) =
      -(value (Y0b X F) - D2) by rw [hD2def]; ring, abs_neg]
    have h1 : |D2| ≤ |value (Y0b X F)| + |D2| / 2 ^ 53 := by
      have h0 := abs_sub_abs_le_abs_sub D2 (value (Y0b X F))
      rw [abs_sub_comm D2] at h0
      linarith only [h0, hYbe]
    have hn := abs_nonneg D2
    have h2 : |D2| / 2 ^ 53 ≤ |D2| / 2 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
    have h3 : |D2| ≤ 2 * |value (Y0b X F)| := by linarith only [h1, h2, hn]
    have h4 : |D2| / 2 ^ 53 ≤ 2 * |value (Y0b X F)| / 2 ^ 53 :=
      div_le_div_of_nonneg_right h3 (by norm_num)
    have h5 : 2 * |value (Y0b X F)| / 2 ^ 53 = |value (Y0b X F)| / 2 ^ 52 := by ring
    have h6 : |value (Y0b X F) - D2| ≤ |D2| / 2 ^ 53 := hYbe
    linarith only [h4, h5, h6]

#print axioms step2
#print axioms caseB

end Verified.Examples.TrigMediumB
