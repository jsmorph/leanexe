import Verified.Examples.TrigMediumB

/-!
The third outcome of the medium reduction: when the second step also cancels below `x / 2 ^ 49`,
the second difference is exact, and `y0 + y1 = R3 - W3'` lies within `x / 2 ^ 151` of
`r = x - N π/2`, which is at least `2 ^ -63` in magnitude.
-/

namespace Verified.Examples.TrigMediumC

open CodeLib.IEEE64 LeanExe.ProofKit TrigFloatTools TrigNearest TrigSmall TrigMediumConst
  TrigMediumCases TrigMediumB

theorem caseC (X F : UInt64) (N : Nat) (h : Med X F N)
    (hgo : Wasm.IEEE64.exponent (Y0 X F) + 16 < Wasm.IEEE64.exponent X)
    (hgo2 : Wasm.IEEE64.exponent (Y0b X F) + 49 < Wasm.IEEE64.exponent X) :
    Finite (Y0c X F) ∧ Finite (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R3 X F) (Y0c X F)) (W3' X F)) ∧
      |value (Y0c X F) + value (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R3 X F) (Y0c X F)) (W3' X F)) -
          (value X - N * (Real.pi / 2))| ≤ |value X - N * (Real.pi / 2)| / 2 ^ 60 ∧
      |value (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R3 X F) (Y0c X F)) (W3' X F))| ≤
        |value (Y0c X F)| / 2 ^ 52 := by
  obtain ⟨hW2f, hW2v, hW2d, hR2f, hR2d, hR2e, hW2'f, hW2'b, hD2r⟩ := step2 X F N h hgo
  obtain ⟨hrl, hru, hNle, hE1, hE2, hRf, hRv, hRd, -, -, -⟩ := med_common X F N h
  obtain ⟨-, hP2, hP3, -, -, -, -, hP3tl, hP3tu⟩ := pio2_values
  obtain ⟨-, -, -, -, hP3f, hP3tf, -, -, hs3, -, -, -, -, -, -⟩ := consts_checked
  have hp3 := pio2_3_close
  rw [abs_le] at hp3
  have hpi4 : Real.pi < 3.15 := Real.pi_lt_d2
  have hx1 := h.x1
  have hx0 : 0 < value X := by linarith
  have hx21 : value X ≤ 2 ^ 21 := by
    have h2pi : 0.6 ≤ 2 / Real.pi := by
      rw [le_div_iff₀ (by linarith [Real.pi_gt_three])]
      linarith
    have h6 : value X * 0.6 ≤ 2 ^ 20 := le_trans (mul_le_mul_of_nonneg_left h2pi hx0.le) h.x2
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.N1
  have hN2 : (N : ℝ) ≤ 2 ^ 20 := by exact_mod_cast h.N2
  have hP3t0 : 0 ≤ value pio2_3t := le_trans (by norm_num) hP3tl
  have hFv : value F = N := by
    rw [TrigSmall.value_of_scaled, h.Fv]
    push_cast
    rw [mul_div_assoc, div_self (pow_ne_zero _ (by norm_num)), mul_one]
  set r := value X - N * (Real.pi / 2) with hrdef
  set D2 := value (R2 X F) - value (W2' X F) with hD2def
  -- The second step cancelled below `x / 2 ^ 49`.
  have hYb := exp_upper (Y0b X F) X 49 (by omega) hgo2
  rw [abs_of_pos hx0] at hYb
  have hD2u : |D2| ≤ 1 := by
    have := abs_add_le r (D2 - r)
    rw [show r + (D2 - r) = D2 by ring] at this
    have h1 : value X / 2 ^ 118 ≤ 2 ^ 21 / 2 ^ 118 := div_le_div_of_nonneg_right hx21 (by norm_num)
    have : (2 : ℝ) ^ 21 / 2 ^ 118 ≤ 1 / 100 := by norm_num
    linarith
  obtain ⟨-, hYbe⟩ := sub_rel (R2 X F) (W2' X F) hR2f hW2'f
    (lt_of_le_of_lt hD2u (one_lt_pow₀ (by norm_num) (by norm_num)))
  have hYbd : Y0b X F = Wasm.IEEE64.sub (R2 X F) (W2' X F) := rfl
  rw [← hD2def, ← hYbd] at hYbe
  have hD2s : |D2| ≤ value X / 2 ^ 48 := by
    have h1 : |D2| ≤ |value (Y0b X F)| + |D2| / 2 ^ 53 := by
      have h0 := abs_sub_abs_le_abs_sub D2 (value (Y0b X F))
      rw [abs_sub_comm D2] at h0
      linarith only [h0, hYbe]
    have h2 : |D2| / 2 ^ 53 ≤ |D2| / 2 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
      (by norm_num)
    have e : value X / 2 ^ 48 = 2 * (value X / 2 ^ 49) := by ring
    linarith only [h1, h2, e, hYb]
  have hR2s : |value (R2 X F)| ≤ value X / 2 ^ 47 := by
    have h1 := abs_add_le D2 (value (W2' X F))
    rw [show D2 + value (W2' X F) = value (R2 X F) by rw [hD2def]; ring] at h1
    have h2 : value X / 2 ^ 65 ≤ value X / 2 ^ 48 :=
      div_le_div_of_nonneg_left hx0.le (by norm_num) (by norm_num)
    have e : value X / 2 ^ 47 = value X / 2 ^ 48 + value X / 2 ^ 48 := by ring
    linarith only [h1, h2, e, hD2s, hW2'b]
  -- The second difference is exact.
  have hR1W2 : |value (R1 X F) - value (W2 F)| ≤ value X / 2 ^ 46 := by
    have h1 := abs_sub (value (R2 X F)) (value (R2 X F) - (value (R1 X F) - value (W2 F)))
    rw [show value (R2 X F) - (value (R2 X F) - (value (R1 X F) - value (W2 F))) =
      value (R1 X F) - value (W2 F) by ring] at h1
    have h2 : value X / 2 ^ 67 ≤ value X / 2 ^ 47 :=
      div_le_div_of_nonneg_left hx0.le (by norm_num) (by norm_num)
    have e : value X / 2 ^ 46 = value X / 2 ^ 47 + value X / 2 ^ 47 := by ring
    linarith only [h1, h2, e, hR2s, hR2e]
  obtain ⟨-, hR2v⟩ := sub_exact (R1 X F) (W2 F) hRf hW2f 1009 (by norm_num) hRd hW2d (by
    have e : (2 : ℝ) ^ (53 + 1009) / 2 ^ 1074 = 1 / 2 ^ 12 := by
      rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
    rw [e]
    have h1 : value X / 2 ^ 46 ≤ 2 ^ 21 / 2 ^ 46 := div_le_div_of_nonneg_right hx21 (by norm_num)
    have : (2 : ℝ) ^ 21 / 2 ^ 46 ≤ 1 / 2 ^ 12 := by norm_num
    linarith only [h1, this, hR1W2])
  have hR2d' : R2 X F = Wasm.IEEE64.sub (R1 X F) (W2 F) := rfl
  rw [← hR2d'] at hR2v
  -- `W3 = N · pio2_3`, exact, and `A3 ≈ N · pio2_3t`.
  obtain ⟨hW3f, hW3s⟩ := mul_count F pio2_3 N 160220439 978 h.Ff hP3f h.Fv h.N1 h.N2 hs3
    (by norm_num) (by norm_num) (by norm_num)
  have hW3v : value (W3 F) = N * value pio2_3 := by
    rw [W3, TrigSmall.value_of_scaled, hW3s, hP3]
    push_cast
    rw [show (1074 : Nat) = 978 + 96 by norm_num, pow_add]
    field_simp
  have hW3d : (2 : Int) ^ 978 ∣ Wasm.IEEE64.scaledValue (W3 F) := by
    rw [W3, hW3s]
    exact Dvd.intro_left _ rfl
  have hNt : |value F * value pio2_3t| = N * value pio2_3t := by
    rw [hFv, abs_of_nonneg (mul_nonneg hN0 hP3t0)]
  obtain ⟨hA3f, hA3e⟩ := mul_rel F pio2_3t h.Ff hP3tf (by
      rw [hNt]
      have h900 : (1 : ℝ) / 2 ^ 900 ≤ 1 / 2 ^ 104 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
      calc (1 : ℝ) / 2 ^ 900 ≤ 1 * (1 / 2 ^ 104) := by rw [one_mul]; exact h900
        _ ≤ N * value pio2_3t := mul_le_mul hN1 hP3tl (by norm_num) hN0)
    (by
      rw [hNt]
      calc (N : ℝ) * value pio2_3t ≤ 2 ^ 20 * (1 / 2 ^ 103) :=
            mul_le_mul hN2 hP3tu hP3t0 (by norm_num)
        _ ≤ 2 ^ 100 := by norm_num)
  rw [hNt, hFv] at hA3e
  replace hA3e : |value (A3 F) - N * value pio2_3t| ≤ N * value pio2_3t / 2 ^ 52 := hA3e
  replace hA3f : Finite (A3 F) := hA3f
  have hA3 : |value (A3 F)| ≤ value X / 2 ^ 102 := by
    have h1 : (N : ℝ) * value pio2_3t ≤ 6 / 5 * value X * (1 / 2 ^ 103) :=
      mul_le_mul hNle hP3tu hP3t0 (by linarith)
    have h2 : |value (A3 F)| ≤ N * value pio2_3t + N * value pio2_3t / 2 ^ 52 := by
      have h0 := abs_sub_abs_le_abs_sub (value (A3 F)) (N * value pio2_3t)
      rw [abs_of_nonneg (mul_nonneg hN0 hP3t0)] at h0
      linarith only [h0, hA3e]
    have h3 : (N : ℝ) * value pio2_3t / 2 ^ 52 ≤ 6 / 5 * value X * (1 / 2 ^ 103) / 2 ^ 52 :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have e : value X / 2 ^ 102 = value X * (1 / 2 ^ 102) := by ring
    have e2 : 6 / 5 * value X * (1 / 2 ^ 103) + 6 / 5 * value X * (1 / 2 ^ 103) / 2 ^ 52 =
        value X * (6 / 5 / 2 ^ 103 * (1 + 1 / 2 ^ 52)) := by ring
    have h4 : value X * (6 / 5 / 2 ^ 103 * (1 + 1 / 2 ^ 52)) ≤ value X * (1 / 2 ^ 102) :=
      mul_le_mul_of_nonneg_left (by norm_num) hx0.le
    linarith only [h1, h2, h3, e, e2, h4]
  -- The third step.
  have hW3b : |value (W3 F)| ≤ 1 / 2 ^ 48 := by
    rw [hW3v, abs_of_nonneg (mul_nonneg hN0 (by rw [hP3]; positivity)), hP3]
    calc (N : ℝ) * (160220439 / 2 ^ 96) ≤ 2 ^ 20 * (160220439 / 2 ^ 96) :=
          mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ ≤ 1 / 2 ^ 48 := by norm_num
  have hB3 : |value (R2 X F) - value (W3 F)| ≤ value X / 2 ^ 46 := by
    have h1 := abs_sub (value (R2 X F)) (value (W3 F))
    have h2 : (1 : ℝ) / 2 ^ 48 ≤ value X / 2 ^ 48 := div_le_div_of_nonneg_right hx1 (by norm_num)
    have h3 : value X / 2 ^ 48 ≤ value X / 2 ^ 47 :=
      div_le_div_of_nonneg_left hx0.le (by norm_num) (by norm_num)
    have e : value X / 2 ^ 46 = value X / 2 ^ 47 + value X / 2 ^ 47 := by ring
    linarith only [h1, h2, h3, e, hR2s, hW3b]
  have hB3s : value X / 2 ^ 46 ≤ 1 := by
    rw [div_le_one (by norm_num)]
    calc value X ≤ 2 ^ 21 := hx21
      _ ≤ 2 ^ 46 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hB32 : value X / 2 ^ 46 < 2 ^ 1000 := lt_of_le_of_lt hB3s (one_lt_pow₀ (by norm_num)
    (by norm_num))
  have hfit : |value (W3 F)| + value X / 2 ^ 46 / 2 ^ 53 ≤ (2 : ℝ) ^ (53 + 978) / 2 ^ 1074 := by
    have e : (2 : ℝ) ^ (53 + 978) / 2 ^ 1074 = 1 / 2 ^ 43 := by
      rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
    rw [e]
    have h2 : value X / 2 ^ 46 / 2 ^ 53 ≤ 1 / 2 ^ 53 := div_le_div_of_nonneg_right hB3s (by norm_num)
    have : (1 : ℝ) / 2 ^ 48 + 1 / 2 ^ 53 ≤ 1 / 2 ^ 43 := by norm_num
    linarith only [h2, this, hW3b]
  have hAe : |value (A3 F)| + value X / 2 ^ 46 / 2 ^ 53 < 2 ^ 1000 := by
    have h1 : value X / 2 ^ 102 ≤ 1 := by
      rw [div_le_one (by norm_num)]
      calc value X ≤ 2 ^ 21 := hx21
        _ ≤ 2 ^ 102 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h2 : value X / 2 ^ 46 / 2 ^ 53 ≤ 1 := by
      rw [div_le_one (by norm_num)]
      exact le_trans hB3s (one_le_pow₀ (by norm_num))
    have h3 : |value (A3 F)| + value X / 2 ^ 46 / 2 ^ 53 ≤ 2 := by linarith only [h1, h2, hA3]
    exact lt_of_le_of_lt h3 (lt_of_lt_of_le (by norm_num : (2 : ℝ) < 2 ^ 2)
      (pow_le_pow_right₀ (by norm_num) (by norm_num)))
  obtain ⟨hR3f, -, hR3e, hE3f, hE3v, hW3'f, hW3'e⟩ := comp_step (R2 X F) (W3 F) (A3 F) 978
    (by norm_num) hR2f hW3f hA3f (dvd_trans (pow_dvd_pow 2 (by norm_num)) hR2d) hW3d
    (value X / 2 ^ 46) hB3 hB32 hfit hAe
  have hR3 : R3 X F = Wasm.IEEE64.sub (R2 X F) (W3 F) := rfl
  have hW3' : W3' X F = Wasm.IEEE64.sub (A3 F)
      (Wasm.IEEE64.sub (Wasm.IEEE64.sub (R2 X F) (R3 X F)) (W3 F)) := rfl
  rw [← hR3] at hR3f hR3e hE3f hE3v hW3'f hW3'e
  rw [← hW3'] at hW3'f hW3'e
  set E3 := value (R2 X F) - value (W3 F) - value (R3 X F) with hE3def
  set D3 := value (R3 X F) - value (W3' X F) with hD3def
  have hB53 : value X / 2 ^ 46 / 2 ^ 53 = value X / 2 ^ 99 := by ring
  rw [hB53] at hR3e hW3'e
  have hE3 : |E3| ≤ value X / 2 ^ 99 := by
    rw [hE3def, show value (R2 X F) - value (W3 F) - value (R3 X F) =
      -(value (R3 X F) - (value (R2 X F) - value (W3 F))) by ring, abs_neg]
    exact hR3e
  have hdel : |value (W3' X F) - (value (A3 F) - E3)| ≤
      (value X / 2 ^ 102 + value X / 2 ^ 99) / 2 ^ 53 :=
    hW3'e.trans (div_le_div_of_nonneg_right (by linarith only [hA3]) (by norm_num))
  have hD3r : |D3 - r| ≤ value X / 2 ^ 151 := by
    have e : D3 - r = (N * (Real.pi / 2 - value pio2_1 - value pio2_2 - value pio2_3 -
        value pio2_3t)) - (value (A3 F) - N * value pio2_3t) -
        (value (W3' X F) - (value (A3 F) - E3)) := by
      rw [hD3def, hrdef, hE3def, hR2v, hRv, hW2v, hW3v]
      ring
    rw [e]
    have h1 : |(N : ℝ) * (Real.pi / 2 - value pio2_1 - value pio2_2 - value pio2_3 -
        value pio2_3t)| ≤ N * (1 / 2 ^ 157) := by
      rw [abs_mul, abs_of_nonneg hN0]
      apply mul_le_mul_of_nonneg_left _ hN0
      rw [abs_le]
      constructor <;> linarith
    have h2 : |value (A3 F) - N * value pio2_3t| ≤ N * (1 / 2 ^ 103) / 2 ^ 52 :=
      hA3e.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hP3tu hN0) (by norm_num))
    have h3 := abs_sub (N * (Real.pi / 2 - value pio2_1 - value pio2_2 - value pio2_3 -
      value pio2_3t)) (value (A3 F) - N * value pio2_3t)
    have h4 := abs_sub (N * (Real.pi / 2 - value pio2_1 - value pio2_2 - value pio2_3 -
      value pio2_3t) - (value (A3 F) - N * value pio2_3t)) (value (W3' X F) - (value (A3 F) - E3))
    have h5 : (N : ℝ) * (1 / 2 ^ 157) + N * (1 / 2 ^ 103) / 2 ^ 52 +
        (value X / 2 ^ 102 + value X / 2 ^ 99) / 2 ^ 53 ≤ value X / 2 ^ 151 := by
      have e2 : (N : ℝ) * (1 / 2 ^ 157) + N * (1 / 2 ^ 103) / 2 ^ 52 = N * (5 / 2 ^ 157) := by
        ring
      rw [e2]
      have h6 : (N : ℝ) * (5 / 2 ^ 157) ≤ 6 / 5 * value X * (5 / 2 ^ 157) :=
        mul_le_mul_of_nonneg_right hNle (by norm_num)
      have e3 : 6 / 5 * value X * (5 / 2 ^ 157) + (value X / 2 ^ 102 + value X / 2 ^ 99) / 2 ^ 53 =
          value X * (6 / 2 ^ 157 + 1 / 2 ^ 155 + 1 / 2 ^ 152) := by ring
      have e4 : value X / 2 ^ 151 = value X * (1 / 2 ^ 151) := by ring
      have h7 : value X * (6 / 2 ^ 157 + 1 / 2 ^ 155 + 1 / 2 ^ 152) ≤ value X * (1 / 2 ^ 151) :=
        mul_le_mul_of_nonneg_left (by norm_num) hx0.le
      linarith only [h6, e3, e4, h7]
    linarith only [h1, h2, h3, h4, h5, hdel]
  -- `y0` of the third step and the exact two-sum.
  have hsmallX : value X / 2 ^ 151 ≤ 1 / 2 ^ 130 := by
    calc value X / 2 ^ 151 ≤ 2 ^ 21 / 2 ^ 151 := div_le_div_of_nonneg_right hx21 (by norm_num)
      _ = 1 / 2 ^ 130 := by norm_num
  have hD3u : |D3| ≤ 1 := by
    have := abs_add_le r (D3 - r)
    rw [show r + (D3 - r) = D3 by ring] at this
    have : (1 : ℝ) / 2 ^ 130 ≤ 1 / 100 := by norm_num
    linarith
  obtain ⟨-, hYce⟩ := sub_rel (R3 X F) (W3' X F) hR3f hW3'f
    (lt_of_le_of_lt hD3u (one_lt_pow₀ (by norm_num) (by norm_num)))
  have hYc : Y0c X F = Wasm.IEEE64.sub (R3 X F) (W3' X F) := rfl
  rw [← hD3def, ← hYc] at hYce
  have hW3'b : |value (W3' X F)| ≤ 1 / 2 ^ 76 := by
    have h1 := abs_sub_abs_le_abs_sub (value (W3' X F)) (value (A3 F) - E3)
    have h2 := abs_sub (value (A3 F)) E3
    have h3 : (value X / 2 ^ 102 + value X / 2 ^ 99) / 2 ^ 53 ≤ value X / 2 ^ 99 := by
      have e : (value X / 2 ^ 102 + value X / 2 ^ 99) / 2 ^ 53 ≤ (value X / 2 ^ 99 + value X / 2 ^ 99) / 2 ^ 53 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        have := div_le_div_of_nonneg_left hx0.le (show (0 : ℝ) < 2 ^ 99 by norm_num)
          (show (2 : ℝ) ^ 99 ≤ 2 ^ 102 by norm_num)
        linarith
      have e2 : (value X / 2 ^ 99 + value X / 2 ^ 99) / 2 ^ 53 = value X / 2 ^ 99 / 2 ^ 52 := by ring
      have e3 : value X / 2 ^ 99 / 2 ^ 52 ≤ value X / 2 ^ 99 := div_le_self (by positivity) (by norm_num)
      linarith
    have h4 : value X / 2 ^ 102 ≤ value X / 2 ^ 99 :=
      div_le_div_of_nonneg_left hx0.le (by norm_num) (by norm_num)
    have h5 : value X / 2 ^ 99 ≤ 2 ^ 21 / 2 ^ 99 := div_le_div_of_nonneg_right hx21 (by norm_num)
    have : (3 : ℝ) * (2 ^ 21 / 2 ^ 99) ≤ 1 / 2 ^ 76 := by norm_num
    linarith only [h1, h2, h3, h4, h5, this, hA3, hE3, hdel]
  have hD3lo : 1 / 2 ^ 63 - 1 / 2 ^ 130 ≤ |D3| := by
    have := abs_sub_abs_le_abs_sub r (r - D3)
    rw [show r - (r - D3) = D3 by ring, abs_sub_comm r D3] at this
    linarith only [this, hrl, hD3r, hsmallX]
  have hR3W : 4 * |value (W3' X F)| ≤ |value (R3 X F)| := by
    have := abs_sub_abs_le_abs_sub D3 (-value (W3' X F))
    rw [show D3 - -value (W3' X F) = value (R3 X F) by rw [hD3def]; ring, abs_neg] at this
    have : (5 : ℝ) * (1 / 2 ^ 76) ≤ 1 / 2 ^ 63 - 1 / 2 ^ 130 := by norm_num
    linarith
  have hR3big : |value (R3 X F)| < 2 ^ 1020 := by
    have h1 := abs_add_le D3 (value (W3' X F))
    rw [show D3 + value (W3' X F) = value (R3 X F) by rw [hD3def]; ring] at h1
    have : (1 : ℝ) / 2 ^ 76 ≤ 1 := by norm_num
    have h3 : |value (R3 X F)| ≤ 2 := by linarith
    exact lt_of_le_of_lt h3 (lt_of_lt_of_le (by norm_num : (2 : ℝ) < 2 ^ 2)
      (pow_le_pow_right₀ (by norm_num) (by norm_num)))
  obtain ⟨hYcf, -, hdf, hdv, hef, hev⟩ := small_two_diff (R3 X F) (W3' X F) hR3f hW3'f hR3W hR3big
  rw [← hYc] at hYcf hdf hdv hef hev
  refine ⟨hYcf, hef, ?_, ?_⟩
  · rw [hev, show value (Y0c X F) + (value (R3 X F) - value (W3' X F) - value (Y0c X F)) - r =
      D3 - r by rw [hD3def]; ring]
    have h1 : (1 : ℝ) / 2 ^ 130 ≤ 1 / 2 ^ 63 / 2 ^ 67 := by norm_num
    have h2 : (1 : ℝ) / 2 ^ 63 / 2 ^ 67 ≤ |r| / 2 ^ 67 := div_le_div_of_nonneg_right hrl (by norm_num)
    have h3 : |r| / 2 ^ 67 ≤ |r| / 2 ^ 60 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
      (by norm_num)
    linarith only [hD3r, hsmallX, h1, h2, h3]
  · rw [hev, show value (R3 X F) - value (W3' X F) - value (Y0c X F) =
      -(value (Y0c X F) - D3) by rw [hD3def]; ring, abs_neg]
    have h1 : |D3| ≤ |value (Y0c X F)| + |D3| / 2 ^ 53 := by
      have h0 := abs_sub_abs_le_abs_sub D3 (value (Y0c X F))
      rw [abs_sub_comm D3] at h0
      linarith only [h0, hYce]
    have hn := abs_nonneg D3
    have h2 : |D3| / 2 ^ 53 ≤ |D3| / 2 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
    have h3 : |D3| ≤ 2 * |value (Y0c X F)| := by linarith only [h1, h2, hn]
    have h4 : |D3| / 2 ^ 53 ≤ 2 * |value (Y0c X F)| / 2 ^ 53 :=
      div_le_div_of_nonneg_right h3 (by norm_num)
    have h5 : 2 * |value (Y0c X F)| / 2 ^ 53 = |value (Y0c X F)| / 2 ^ 52 := by ring
    linarith only [h4, h5, hYce]

#print axioms caseC

end Verified.Examples.TrigMediumC
