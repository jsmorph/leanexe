import Verified.Examples.TgammaRecip
import Verified.Examples.TgammaFloor

/-!
The reciprocal of a double-double `wh + wl` in `tgammaWith` on `(-3, 4)`: `rh = 1/wh` and the
correction `c = (fma rh (-wh) 1 - wl rh) rh`.  With `D = wh + wl` and `E = 1 - rh D`, the exact
correction is `E rh`, and `rh + E rh - 1/D = -E²/D`.  For `|wl| ≤ 2 ^ -40 |wh|`, `|E|` stays below
`(5/4) 2 ^ -40`, so `rh + c` lies within `2 ^ -78` of `1/D` relative (`recip_dd`).
-/

namespace Verified.Examples.TgammaRecipDD
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx TgammaDD TgammaRecip TgammaFloor

set_option exponentiation.threshold 4096

/-- **The corrected reciprocal of a double-double.** -/
theorem recip_dd (hF : FmaSpec.FmaNearest) (wh wl : Float) (hwh : Finite wh.toBits)
    (hwl : Finite wl.toBits) (hk : |value wl.toBits| ≤ |value wh.toBits| / 2 ^ 40)
    (hlo : 1 / 2 ^ 600 ≤ |value wh.toBits|) (hhi : |value wh.toBits| ≤ 2 ^ 600) :
    Finite (1.0 / wh).toBits ∧
      Finite ((Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh)).toBits ∧
      |value (1.0 / wh).toBits +
          value ((Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh)).toBits -
          1 / (value wh.toBits + value wl.toBits)| ≤
        |1 / (value wh.toBits + value wl.toBits)| / 2 ^ 78 ∧
      |value ((Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh)).toBits| ≤
        |value (1.0 / wh).toBits| / 2 ^ 38 ∧
      |value (1.0 / wh).toBits| ≤ |1 / (value wh.toBits + value wl.toBits)| * (1 + 1 / 2 ^ 38) := by
  obtain ⟨vh, hvh⟩ : ∃ v, v = value wh.toBits := ⟨_, rfl⟩
  obtain ⟨vl, hvl⟩ : ∃ v, v = value wl.toBits := ⟨_, rfl⟩
  rw [← hvh, ← hvl] at hk ⊢
  rw [← hvh] at hlo hhi
  have hvh0 : 0 < |vh| := lt_of_lt_of_le (by positivity) hlo
  obtain ⟨R, hR⟩ : ∃ R, R = 1 / |vh| := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hR]; positivity
  have hRvh : R * |vh| = 1 := by rw [hR]; field_simp
  have hRlo : 1 / 2 ^ 600 ≤ R := by
    rw [hR, div_le_div_iff₀ (by positivity) hvh0]
    linarith
  have hRhi : R ≤ 2 ^ 600 := by
    rw [hR, div_le_iff₀ hvh0]
    calc (1 : ℝ) = 2 ^ 600 * (1 / 2 ^ 600) := by norm_num
      _ ≤ 2 ^ 600 * |vh| := by gcongr
  have hRabs : |1 / vh| = R := by rw [abs_div, abs_one, hR]
  -- `rh = 1/wh`
  have hr0 := fapprox_div (fapprox_self _ one_finite) (fapprox_self wh hwh) 1 |vh|
    (by rw [one_value, abs_one]) (by rw [← hvh]) hvh0 R (by rw [hR]; simp)
    (by linarith [(by norm_num : (2 : ℝ) ^ 600 < 2 ^ 1022)])
  rw [one_value, ← hvh] at hr0
  have hr : FApprox (1.0 / wh) (1 / vh) (R / 2 ^ 52) := by
    refine Approx.mono hr0 ?_
    have : (0 + 1 * 0 / |vh|) / (|vh| - 0) = 0 := by simp
    rw [this, zero_add]
    have : (1 : ℝ) / 2 ^ 1075 ≤ R / 2 ^ 53 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [(by norm_num : (2 : ℝ) ^ 53 ≤ 1 / 2 ^ 600 * 2 ^ 1075)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 53 + 1 / 2 ^ 53 = 1 / 2 ^ 52),
      (by ring : R / 2 ^ 53 + R / 2 ^ 53 = R / 2 ^ 52)]
  obtain ⟨vr, hvr⟩ : ∃ v, v = value (1.0 / wh).toBits := ⟨_, rfl⟩
  have hre : |vr - 1 / vh| ≤ R / 2 ^ 52 := by rw [hvr]; exact hr.2
  have hvr_hi : |vr| ≤ R * (1 + 1 / 2 ^ 52) := by
    have := abs_sub_abs_le_abs_sub vr (1 / vh)
    rw [hRabs] at this
    linarith
  have hvr_lo : R * (1 - 1 / 2 ^ 52) ≤ |vr| := by
    have := abs_sub_abs_le_abs_sub (1 / vh) vr
    rw [hRabs, abs_sub_comm] at this
    linarith
  -- the residual `S = 1 - rh wh`, computed by the fused multiply-add
  obtain ⟨hnf, hnv⟩ := neg_float wh hwh
  rw [← hvh] at hnv
  have hvh_ne : vh ≠ 0 := abs_pos.mp hvh0
  have hSv : vr * (-vh) + 1 = -vh * (vr - 1 / vh) := by field_simp; ring
  have hSb : |vr * (-vh) + 1| ≤ 1 / 2 ^ 52 := by
    rw [hSv, abs_mul, abs_neg]
    calc |vh| * |vr - 1 / vh| ≤ |vh| * (R / 2 ^ 52) := mul_le_mul_of_nonneg_left hre (abs_nonneg _)
      _ = R * |vh| / 2 ^ 52 := by ring
      _ = 1 / 2 ^ 52 := by rw [hRvh]
  have ht := fma_approx hF (1.0 / wh) (-wh) 1.0 hr.1 hnf one_finite
    (by rw [← hvr, hnv, one_value]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 2 ^ 1000)])
  rw [← hvr, hnv, one_value] at ht
  have ht' : FApprox (Fma.fma (1.0 / wh) (-wh) 1.0) (vr * (-vh) + 1) (1 / 2 ^ 104) := by
    refine Approx.mono ht ?_
    have : |vr * (-vh) + 1| / 2 ^ 53 ≤ 1 / 2 ^ 105 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 105 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 104)]
  -- `u = wl rh`
  have hlr : |vl| * |vr| ≤ (1 + 1 / 2 ^ 52) / 2 ^ 40 := by
    calc |vl| * |vr| ≤ (|vh| / 2 ^ 40) * (R * (1 + 1 / 2 ^ 52)) :=
          mul_le_mul hk hvr_hi (abs_nonneg _) (by positivity)
      _ = R * |vh| * (1 + 1 / 2 ^ 52) / 2 ^ 40 := by ring
      _ = (1 + 1 / 2 ^ 52) / 2 ^ 40 := by rw [hRvh, one_mul]
  have hu0 := fapprox_mul (fapprox_self wl hwl) (fapprox_self (1.0 / wh) hr.1) |vl| |vr|
    (by rw [← hvl]) (by rw [← hvr]) (|vl| * |vr|) (by simp)
    (by linarith [(by norm_num : (1 + 1 / 2 ^ 52 : ℝ) / 2 ^ 40 < 2 ^ 1022)])
  rw [← hvl, ← hvr] at hu0
  have hu : FApprox (wl * (1.0 / wh)) (vl * vr) (1 / 2 ^ 92) := by
    refine Approx.mono hu0 ?_
    simp only [zero_mul, mul_zero, add_zero, zero_add]
    linarith [(by norm_num : (1 + 1 / 2 ^ 52 : ℝ) / 2 ^ 40 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 92)]
  -- `v = S - u` and `c = v rh`
  have hE : |vr * (-vh) + 1 - vl * vr| ≤ 5 / 4 / 2 ^ 40 := by
    have := abs_sub (vr * (-vh) + 1) (vl * vr)
    rw [abs_mul vl vr] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 + (1 + 1 / 2 ^ 52) / 2 ^ 40 ≤ 5 / 4 / 2 ^ 40)]
  have hv := fapprox_sub ht' hu (1 / 2 ^ 39) (by linarith [(by norm_num : (5 : ℝ) / 4 / 2 ^ 40 +
      (1 / 2 ^ 104 + 1 / 2 ^ 92) ≤ 1 / 2 ^ 39)]) (by norm_num)
  have hv' : FApprox (Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) (vr * (-vh) + 1 - vl * vr)
      (1 / 2 ^ 90) := Approx.mono hv (by norm_num)
  have hc0 := fapprox_mul hv' (fapprox_self (1.0 / wh) hr.1) (5 / 4 / 2 ^ 40) |vr| hE
    (by rw [← hvr]) ((5 / 4 / 2 ^ 40 + 1 / 2 ^ 90) * |vr|) (by rw [add_zero])
    (by nlinarith [(by norm_num : (5 / 4 / 2 ^ 40 + 1 / 2 ^ 90 : ℝ) * (2 ^ 600 * 2) < 2 ^ 1022)])
  rw [← hvr] at hc0
  obtain ⟨vc, hvc⟩ : ∃ v, v = value ((Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) *
    (1.0 / wh)).toBits := ⟨_, rfl⟩
  have hce : |vc - (vr * (-vh) + 1 - vl * vr) * vr| ≤ |vr| / 2 ^ 88 := by
    have h := hc0.2
    rw [← hvc] at h
    simp only [mul_zero, add_zero] at h
    have hvr0 : 0 ≤ |vr| := abs_nonneg _
    have hRvr : R ≤ |vr| * 2 := by linarith
    have : (1 : ℝ) / 2 ^ 1075 ≤ |vr| / 2 ^ 400 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [(by norm_num : (2 : ℝ) ^ 400 ≤ 1 / 2 ^ 600 / 2 * 2 ^ 1075)]
    linarith
  -- the identity `rh + E rh - 1/D = -E²/D`
  set D := vh + vl with hD
  have hDb : |D - vh| ≤ |vh| / 2 ^ 40 := by rw [hD, add_sub_cancel_left]; exact hk
  have hD_lo : |vh| * (1 - 1 / 2 ^ 40) ≤ |D| := by
    have := abs_sub_abs_le_abs_sub vh D
    rw [abs_sub_comm] at this
    linarith
  have hD_hi : |D| ≤ |vh| * (1 + 1 / 2 ^ 40) := by
    have := abs_sub_abs_le_abs_sub D vh
    linarith
  have hD0 : 0 < |D| := lt_of_lt_of_le (by positivity) hD_lo
  have hD_ne : D ≠ 0 := abs_pos.mp hD0
  have hiD : |1 / D| = 1 / |D| := by rw [abs_div, abs_one]
  have hR_iD : R ≤ |1 / D| * (1 + 1 / 2 ^ 40) := by
    rw [hiD, hR, show 1 / |D| * (1 + 1 / 2 ^ 40) = (1 + 1 / 2 ^ 40) / |D| by ring,
      div_le_div_iff₀ hvh0 hD0]
    linarith
  have hD_ne' : vh + vl ≠ 0 := hD_ne
  have hid : vr + (vr * (-vh) + 1 - vl * vr) * vr - 1 / D =
      -((vr * (-vh) + 1 - vl * vr) ^ 2) * (1 / D) := by
    rw [hD]
    field_simp
    ring
  have hE2 : (vr * (-vh) + 1 - vl * vr) ^ 2 ≤ 1 / 2 ^ 79 := by
    rw [← sq_abs]
    calc |vr * (-vh) + 1 - vl * vr| ^ 2 ≤ (5 / 4 / 2 ^ 40) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hE 2
      _ ≤ 1 / 2 ^ 79 := by norm_num
  have hiD0 : 0 ≤ |1 / D| := abs_nonneg _
  refine ⟨hr.1, hc0.1, ?_, ?_, ?_⟩
  · rw [← hvr, ← hvc]
    have h1 : |vr + (vr * (-vh) + 1 - vl * vr) * vr - 1 / D| ≤ 1 / 2 ^ 79 * |1 / D| := by
      rw [hid, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right hE2 hiD0
    have h2 := abs_add_le (vr + (vr * (-vh) + 1 - vl * vr) * vr - 1 / D)
      (vc - (vr * (-vh) + 1 - vl * vr) * vr)
    rw [show vr + (vr * (-vh) + 1 - vl * vr) * vr - 1 / D + (vc - (vr * (-vh) + 1 - vl * vr) * vr) =
      vr + vc - 1 / D by ring] at h2
    linarith
  · rw [← hvr, ← hvc]
    have h1 := abs_sub_abs_le_abs_sub vc ((vr * (-vh) + 1 - vl * vr) * vr)
    have h2 : |(vr * (-vh) + 1 - vl * vr) * vr| ≤ 5 / 4 / 2 ^ 40 * |vr| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hE (abs_nonneg _)
    linarith [abs_nonneg vr]
  · rw [← hvr]
    have := mul_le_mul_of_nonneg_left hR_iD (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 52)
    linarith

#print axioms recip_dd

end Verified.Examples.TgammaRecipDD
