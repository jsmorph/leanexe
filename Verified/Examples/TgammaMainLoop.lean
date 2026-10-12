import Verified.Examples.TgammaMul
import Verified.Examples.TgammaMainRed
import Verified.Examples.TgammaPoly

/-!
The shift loop of `tgammaWith` on `(-3, 4)`.  From `(wh, wl, xph, xpl) = (x, 0, x, 0)`, each step
adds 1 to the double-double `xph + xpl` (`fastTwoSum` and a plain addition to the low part) and
multiplies `wh + wl` by it (`mulDD`), so that after `n` steps `wh + wl` approximates
`W x n = x (x + 1) ⋯ (x + n)`.  The factors can lie within `2 ^ -54` of zero, so the analysis is
relative.  While `x + m < 0`, the low part `xpl` is zero and `xph = x + m` exactly: adding 1 to a
double from -3 to `-1/2` is exact (`shift_step`).  From the first positive factor on, `xpl` stays
below `2 ^ -48 (x + m)`.  Each product adds at most `2 ^ -84` relative error and `2 ^ -46` to the
ratio of the low to the high part (`prod_step`), and `loop_inv` gives the state after `n ≤ 6` steps.
-/

namespace Verified.Examples.TgammaMainLoop
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaMainRed TgammaFloor
  TgammaPoly

set_option exponentiation.threshold 4096

/-- The high part and the error of `xph + 1`, as the loop computes them. -/
def shiftHi (xph : Float) : Float × Float :=
  if xph.abs > 1.0 then fastTwoSum xph 1.0 else fastTwoSum 1.0 xph

theorem shiftHi_spec (xph : Float) (hph : Finite xph.toBits)
    (hlim : |value xph.toBits| < 2 ^ 899) :
    Finite (shiftHi xph).1.toBits ∧ Finite (shiftHi xph).2.toBits ∧
      value (shiftHi xph).1.toBits + value (shiftHi xph).2.toBits = value xph.toBits + 1 ∧
      |value (shiftHi xph).2.toBits| ≤ |value (shiftHi xph).1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074 := by
  obtain ⟨haf, hav⟩ := abs_float xph hph
  by_cases hb : xph.abs > 1.0
  · have hb' : 1 < |value xph.toBits| := by
      rw [GT.gt, F64UpperWord.float_lt_iff _ _ TgammaRecip.one_finite haf, TgammaRecip.one_value,
        hav] at hb
      exact hb
    rw [shiftHi, ite_eq_left hb]
    obtain ⟨h1, h2, h3, -, h5⟩ := fastTwoSum_spec xph 1.0 hph TgammaRecip.one_finite
      (by rw [TgammaRecip.one_value, abs_one]; exact hb'.le) (by linarith)
    rw [TgammaRecip.one_value] at h3
    exact ⟨h1, h2, h3, h5⟩
  · have hb' : |value xph.toBits| ≤ 1 := by
      rw [GT.gt, F64UpperWord.float_lt_iff _ _ TgammaRecip.one_finite haf, TgammaRecip.one_value,
        hav] at hb
      push Not at hb
      exact hb
    rw [shiftHi, ite_eq_right hb]
    obtain ⟨h1, h2, h3, -, h5⟩ := fastTwoSum_spec 1.0 xph TgammaRecip.one_finite hph
      (by rw [TgammaRecip.one_value, abs_one]; exact hb')
      (by rw [TgammaRecip.one_value, abs_one]; norm_num)
    rw [TgammaRecip.one_value] at h3
    exact ⟨h1, h2, by linarith, h5⟩

/-- The high part is `xph + 1` when that sum has at most 53 bits on a grid. -/
theorem shiftHi_exact (xph : Float) (hph : Finite xph.toBits) (z : ℤ) (g : ℕ) (hg : g ≤ 2043)
    (h : (value xph.toBits + 1) * 2 ^ 1074 = z * 2 ^ g) (hz : |(z : ℝ)| ≤ 2 ^ 53) :
    value (shiftHi xph).1.toBits = value xph.toBits + 1 := by
  by_cases hb : xph.abs > 1.0
  · rw [shiftHi, ite_eq_left hb]
    show value (xph + 1.0).toBits = _
    rw [(add_exact xph 1.0 hph TgammaRecip.one_finite z g hg
      (by rw [TgammaRecip.one_value]; exact h) hz).2, TgammaRecip.one_value]
  · rw [shiftHi, ite_eq_right hb]
    show value (1.0 + xph).toBits = _
    rw [(add_exact 1.0 xph TgammaRecip.one_finite hph z g hg
      (by rw [TgammaRecip.one_value, add_comm]; exact h) hz).2, TgammaRecip.one_value, add_comm]

/-- **One shift** of the factor `xph + xpl ≈ F` to `F + 1`. -/
theorem shift_step (xph xpl : Float) (hph : Finite xph.toBits) (hpl : Finite xpl.toBits) (F e : ℝ)
    (hrep : |value xph.toBits + value xpl.toBits - F| ≤ e * |F|)
    (hlow : |value xpl.toBits| ≤ |F| / 2 ^ 48)
    (hneg : F < 0 → value xpl.toBits = 0 ∧ value xph.toBits = F)
    (hF0 : F ≠ 0) (hF3 : -3 ≤ F) (hF4 : F + 1 ≤ 7 / 2) (he0 : 0 ≤ e) (he : e ≤ 1 / 2 ^ 80) :
    Finite (shiftHi xph).1.toBits ∧ Finite (xpl + (shiftHi xph).2).toBits ∧
      |value (shiftHi xph).1.toBits + value (xpl + (shiftHi xph).2).toBits - (F + 1)| ≤
        (e + 1 / 2 ^ 98) * |F + 1| ∧
      |value (xpl + (shiftHi xph).2).toBits| ≤ |F + 1| / 2 ^ 48 ∧
      (F + 1 < 0 →
        value (xpl + (shiftHi xph).2).toBits = 0 ∧ value (shiftHi xph).1.toBits = F + 1) := by
  have hF0' : 0 ≤ |F| := abs_nonneg F
  have heF : e * |F| ≤ |F| / 2 ^ 80 := by
    have := mul_le_mul_of_nonneg_right he hF0'
    linarith
  have hxF : |value xph.toBits - F| ≤ |F| / 2 ^ 47 := by
    have h := abs_sub (value xph.toBits + value xpl.toBits - F) (value xpl.toBits)
    rw [show value xph.toBits + value xpl.toBits - F - value xpl.toBits = value xph.toBits - F by
      ring] at h
    linarith
  have hFb : |F| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hlim : |value xph.toBits| < 2 ^ 899 := by
    have := abs_sub_abs_le_abs_sub (value xph.toBits) F
    linarith [(by norm_num : (3 : ℝ) + 3 / 2 ^ 47 < 2 ^ 899)]
  obtain ⟨hs1, hs2, hsum, hlb⟩ := shiftHi_spec xph hph hlim
  rcases lt_or_gt_of_ne hF0 with hFn | hFp
  · obtain ⟨hpl0, hphF⟩ := hneg hFn
    by_cases hhalf : F ≤ -1 / 2
    · -- adding 1 is exact
      have hsv : value (shiftHi xph).1.toBits = F + 1 := by
        by_cases h2 : F ≤ -2
        · obtain ⟨K, hK⟩ := grid xph.toBits hph 1022 (by norm_num) (by
            rw [hphF, abs_of_neg hFn]
            norm_num
            linarith)
          rw [hphF] at hK
          have hKv : (K : ℝ) = F * 2 ^ 51 := by
            have h' : (K : ℝ) * 2 ^ 1023 = F * 2 ^ 51 * 2 ^ 1023 := by linear_combination -1 * hK
            exact mul_right_cancel₀ (by positivity) h'
          rw [shiftHi_exact xph hph (K + 2 ^ 51) 1023 (by norm_num)
            (by rw [hphF, add_mul, hK]; push_cast; ring)
            (by push_cast; rw [hKv, abs_le]; constructor <;> linarith), hphF]
        · push Not at h2
          obtain ⟨K, hK⟩ := grid xph.toBits hph 1020 (by norm_num) (by
            rw [hphF, abs_of_neg hFn]
            norm_num
            linarith)
          rw [hphF] at hK
          have hKv : (K : ℝ) = F * 2 ^ 53 := by
            have h' : (K : ℝ) * 2 ^ 1021 = F * 2 ^ 53 * 2 ^ 1021 := by linear_combination -1 * hK
            exact mul_right_cancel₀ (by positivity) h'
          rw [shiftHi_exact xph hph (K + 2 ^ 53) 1021 (by norm_num)
            (by rw [hphF, add_mul, hK]; push_cast; ring)
            (by push_cast; rw [hKv, abs_le]; constructor <;> linarith), hphF]
      have hl0 : value (shiftHi xph).2.toBits = 0 := by linarith
      have hx := fapprox_add (fapprox_self xpl hpl) (fapprox_self _ hs2) 0
        (by rw [hpl0, hl0]; norm_num) (by norm_num)
      have hxv : value (xpl + (shiftHi xph).2).toBits = 0 := by
        have h := hx.2
        rw [hpl0, hl0] at h
        have h' : |value (xpl + (shiftHi xph).2).toBits| ≤ 0 := by simpa using h
        exact abs_nonpos_iff.mp h'
      refine ⟨hs1, hx.1, ?_, ?_, fun _ => ⟨hxv, hsv⟩⟩
      · rw [hsv, hxv, add_zero, sub_self, abs_zero]
        exact mul_nonneg (add_nonneg he0 (by positivity)) (abs_nonneg _)
      · rw [hxv, abs_zero]
        positivity
    · -- `F + 1` lies in `(1/2, 1)`
      push Not at hhalf
      have hG : 1 / 2 < F + 1 := by linarith
      have hsum' : value (shiftHi xph).1.toBits + value (shiftHi xph).2.toBits = F + 1 := by
        rw [hsum, hphF]
      have hsb : |value (shiftHi xph).1.toBits| ≤ 2 := by
        have h := abs_sub (F + 1) (value (shiftHi xph).2.toBits)
        rw [show F + 1 - value (shiftHi xph).2.toBits = value (shiftHi xph).1.toBits by linarith,
          abs_of_pos (by linarith : (0 : ℝ) < F + 1)] at h
        linarith
      have hl : |value (shiftHi xph).2.toBits| ≤ 1 / 2 ^ 50 := by
        linarith [(by norm_num : (2 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 50)]
      have hx := fapprox_add (fapprox_self xpl hpl) (fapprox_self _ hs2)
        |value (shiftHi xph).2.toBits| (by simp only [hpl0, zero_add, add_zero, le_refl])
        (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 < 2 ^ 1023)])
      have hxe := hx.2
      simp only [hpl0, zero_add] at hxe
      have hG' : |F + 1| = F + 1 := abs_of_pos (by linarith)
      refine ⟨hs1, hx.1, ?_, ?_, fun h => absurd h (not_lt.mpr (by linarith))⟩
      · rw [hG', show value (shiftHi xph).1.toBits + value (xpl + (shiftHi xph).2).toBits - (F + 1) =
          value (xpl + (shiftHi xph).2).toBits - value (shiftHi xph).2.toBits by linarith]
        have : 0 ≤ e * (F + 1) := mul_nonneg he0 (by linarith)
        have : |value (shiftHi xph).2.toBits| / 2 ^ 53 ≤ 1 / 2 ^ 103 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
      · rw [hG']
        have := abs_sub_abs_le_abs_sub (value (xpl + (shiftHi xph).2).toBits)
          (value (shiftHi xph).2.toBits)
        have : |value (shiftHi xph).2.toBits| / 2 ^ 53 ≤ 1 / 2 ^ 103 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 + 1 / 2 ^ 103 ≤ 1 / 2 / 2 ^ 48)]
  · -- positive factors
    have hG : 1 < F + 1 := by linarith
    have hFa : |F| = F := abs_of_pos hFp
    have hG' : |F + 1| = F + 1 := abs_of_pos (by linarith)
    rw [hFa] at hxF hlow heF
    rw [hG']
    have hsb : |value (shiftHi xph).1.toBits| ≤ 2 * (F + 1) := by
      have h := abs_sub (value xph.toBits + 1) (value (shiftHi xph).2.toBits)
      rw [show value xph.toBits + 1 - value (shiftHi xph).2.toBits = value (shiftHi xph).1.toBits by
        linarith] at h
      have h2 := abs_sub_abs_le_abs_sub (value xph.toBits + 1) (F + 1)
      rw [show value xph.toBits + 1 - (F + 1) = value xph.toBits - F by ring,
        abs_of_pos (by linarith : (0 : ℝ) < F + 1)] at h2
      linarith
    have hl : |value (shiftHi xph).2.toBits| ≤ (F + 1) / 2 ^ 50 := by
      linarith
    have hx := fapprox_add (fapprox_self xpl hpl) (fapprox_self _ hs2)
      (|value xpl.toBits| + |value (shiftHi xph).2.toBits|)
      (by rw [add_zero, add_zero]; exact abs_add_le _ _)
      (by linarith [(by norm_num : (3 : ℝ) / 2 ^ 48 + 4 / 2 ^ 50 < 2 ^ 1023)])
    have hxe := hx.2
    simp only [zero_add] at hxe
    have hr : (|value xpl.toBits| + |value (shiftHi xph).2.toBits|) / 2 ^ 53 ≤ (F + 1) / 2 ^ 100 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine ⟨hs1, hx.1, ?_, ?_, fun h => absurd h (not_lt.mpr (by linarith))⟩
    · rw [show value (shiftHi xph).1.toBits + value (xpl + (shiftHi xph).2).toBits - (F + 1) =
          (value xph.toBits + value xpl.toBits - F) +
            (value (xpl + (shiftHi xph).2).toBits -
              (value xpl.toBits + value (shiftHi xph).2.toBits)) by linarith]
      have h3 := abs_add_le (value xph.toBits + value xpl.toBits - F)
        (value (xpl + (shiftHi xph).2).toBits - (value xpl.toBits + value (shiftHi xph).2.toBits))
      rw [hFa] at hrep
      have : e * F ≤ e * (F + 1) := mul_le_mul_of_nonneg_left (by linarith) he0
      linarith
    · have h3 := abs_sub_abs_le_abs_sub (value (xpl + (shiftHi xph).2).toBits)
        (value xpl.toBits + value (shiftHi xph).2.toBits)
      have h4 := abs_add_le (value xpl.toBits) (value (shiftHi xph).2.toBits)
      have : (F + 1) / 2 ^ 50 + (F + 1) / 2 ^ 100 ≤ 1 / 2 ^ 48 := by
        rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith

/-- The magnitudes of the high parts of the factor and of the product so far. -/
theorem mag_bounds (vxph vxpl vwh vwl F W η θ κ : ℝ) (hP : |vxph + vxpl - F| ≤ η * |F|)
    (hp : |vxpl| ≤ |F| / 2 ^ 48) (hWc : |vwh + vwl - W| ≤ θ * |W|) (hk : |vwl| ≤ κ * |vwh|)
    (hη : η ≤ 1 / 2 ^ 80) (hθ : θ ≤ 1 / 2 ^ 80) (hκ : κ ≤ 1 / 2 ^ 40) :
    |F| * (1 - 1 / 2 ^ 47) ≤ |vxph| ∧ |vxph| ≤ |F| * (1 + 1 / 2 ^ 47) ∧
      |W| * (1 - 1 / 2 ^ 39) ≤ |vwh| ∧ |vwh| ≤ |W| * (1 + 1 / 2 ^ 39) := by
  have hF0 : 0 ≤ |F| := abs_nonneg F
  have hW0 : 0 ≤ |W| := abs_nonneg W
  have hb0 : 0 ≤ |vwh| := abs_nonneg _
  have heF : η * |F| ≤ 1 / 2 ^ 80 * |F| := mul_le_mul_of_nonneg_right hη hF0
  have hθW : θ * |W| ≤ 1 / 2 ^ 80 * |W| := mul_le_mul_of_nonneg_right hθ hW0
  have hκb : κ * |vwh| ≤ 1 / 2 ^ 40 * |vwh| := mul_le_mul_of_nonneg_right hκ hb0
  have hxF : |vxph - F| ≤ |F| / 2 ^ 47 := by
    have h := abs_sub (vxph + vxpl - F) vxpl
    rw [show vxph + vxpl - F - vxpl = vxph - F by ring] at h
    linarith only [h, hP, hp, heF, hF0]
  have hwW : |vwh - W| ≤ |W| / 2 ^ 80 + κ * |vwh| := by
    have h := abs_sub (vwh + vwl - W) vwl
    rw [show vwh + vwl - W - vwl = vwh - W by ring] at h
    linarith only [h, hWc, hk, hθW]
  have h1 := abs_sub_abs_le_abs_sub F vxph
  have h2 := abs_sub_abs_le_abs_sub vxph F
  have h3 := abs_sub_abs_le_abs_sub W vwh
  have h4 := abs_sub_abs_le_abs_sub vwh W
  rw [abs_sub_comm F] at h1
  rw [abs_sub_comm W] at h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [h1, hxF]
  · linarith only [h2, hxF]
  · linarith only [h3, hwW, hκb, hW0, hb0]
  · linarith only [h4, hwW, hκb, hW0]

/-- **One product** of `wh + wl ≈ W` by the factor `xph + xpl ≈ F`, with relative errors. -/
theorem prod_step (hF : FmaSpec.FmaNearest) (xph xpl wh wl : Float) (hph : Finite xph.toBits)
    (hpl : Finite xpl.toBits) (hwh : Finite wh.toBits) (hwl : Finite wl.toBits) (F W η θ κ : ℝ)
    (hP : |value xph.toBits + value xpl.toBits - F| ≤ η * |F|)
    (hp : |value xpl.toBits| ≤ |F| / 2 ^ 48)
    (hWc : |value wh.toBits + value wl.toBits - W| ≤ θ * |W|)
    (hk : |value wl.toBits| ≤ κ * |value wh.toBits|)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 80) (hθ : θ ≤ 1 / 2 ^ 80) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 1 / 2 ^ 40) (hlo : 1 / 2 ^ 900 ≤ |F| * |W|) (hFhi : |F| ≤ 8) (hWhi : |W| ≤ 2 ^ 100) :
    Finite (mulDD xph xpl wh wl).1.toBits ∧ Finite (mulDD xph xpl wh wl).2.toBits ∧
      |value (mulDD xph xpl wh wl).1.toBits + value (mulDD xph xpl wh wl).2.toBits - F * W| ≤
        (η + θ + 1 / 2 ^ 84) * (|F| * |W|) ∧
      |value (mulDD xph xpl wh wl).2.toBits| ≤
        (κ + 1 / 2 ^ 46) * |value (mulDD xph xpl wh wl).1.toBits| := by
  obtain ⟨ha_lo, ha_hi, hb_lo, hb_hi⟩ := mag_bounds _ _ _ _ F W η θ κ hP hp hWc hk hη hθ hκ
  obtain ⟨PV, hPV⟩ : ∃ PV, PV = value xph.toBits + value xpl.toBits := ⟨_, rfl⟩
  obtain ⟨WV, hWV⟩ : ∃ WV, WV = value wh.toBits + value wl.toBits := ⟨_, rfl⟩
  rw [← hPV] at hP
  rw [← hWV] at hWc
  obtain ⟨a, ha⟩ : ∃ a, a = |value xph.toBits| := ⟨_, rfl⟩
  obtain ⟨p, hpd⟩ : ∃ p, p = |value xpl.toBits| := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = |value wh.toBits| := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = |value wl.toBits| := ⟨_, rfl⟩
  rw [← ha] at ha_lo ha_hi
  rw [← hb] at hb_lo hb_hi
  rw [← hpd] at hp
  rw [← hq, ← hb] at hk
  have ha0 : 0 ≤ a := ha ▸ abs_nonneg _
  have hp0 : 0 ≤ p := hpd ▸ abs_nonneg _
  have hb0 : 0 ≤ b := hb ▸ abs_nonneg _
  have hF0 : 0 ≤ |F| := abs_nonneg F
  have hW0 : 0 ≤ |W| := abs_nonneg W
  have hFW0 : 0 ≤ |F| * |W| := mul_nonneg hF0 hW0
  have hFWhi : |F| * |W| ≤ 2 ^ 103 := by
    calc |F| * |W| ≤ 8 * 2 ^ 100 := mul_le_mul hFhi hWhi hW0 (by norm_num)
      _ = 2 ^ 103 := by norm_num
  have hH0lo : |F| * |W| * ((1 - 1 / 2 ^ 47) * (1 - 1 / 2 ^ 39)) ≤ b * a := by
    calc |F| * |W| * ((1 - 1 / 2 ^ 47) * (1 - 1 / 2 ^ 39)) =
        (|W| * (1 - 1 / 2 ^ 39)) * (|F| * (1 - 1 / 2 ^ 47)) := by ring
      _ ≤ b * a := mul_le_mul hb_lo ha_lo (mul_nonneg hF0 (by norm_num)) hb0
  have hH0hi : b * a ≤ |F| * |W| * ((1 + 1 / 2 ^ 47) * (1 + 1 / 2 ^ 39)) := by
    calc b * a ≤ (|W| * (1 + 1 / 2 ^ 39)) * (|F| * (1 + 1 / 2 ^ 47)) :=
          mul_le_mul hb_hi ha_hi ha0 (mul_nonneg hW0 (by norm_num))
      _ = _ := by ring
  have hbF : b * |F| ≤ |F| * |W| * (1 + 1 / 2 ^ 39) := by
    calc b * |F| ≤ (|W| * (1 + 1 / 2 ^ 39)) * |F| := mul_le_mul_of_nonneg_right hb_hi hF0
      _ = _ := by ring
  have hbF' : b * (|F| * (1 - 1 / 2 ^ 47)) ≤ b * a := mul_le_mul_of_nonneg_left ha_lo hb0
  have hP1 : b * p ≤ b * (|F| / 2 ^ 48) := mul_le_mul_of_nonneg_left hp hb0
  have hP2 : q * a ≤ κ * b * a := mul_le_mul_of_nonneg_right hk ha0
  have hP2' : κ * b * a ≤ 1 / 2 ^ 40 * (b * a) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hκ (mul_nonneg hb0 ha0)
  have hL2 : q * p ≤ κ * b * (|F| / 2 ^ 48) := mul_le_mul hk hp hp0 (mul_nonneg hκ0 hb0)
  have hL2' : κ * b * (|F| / 2 ^ 48) ≤ 1 / 2 ^ 40 * (b * |F|) / 2 ^ 48 := by
    have := mul_le_mul_of_nonneg_right hκ (mul_nonneg hb0 hF0)
    rw [show κ * b * (|F| / 2 ^ 48) = κ * (b * |F|) / 2 ^ 48 by ring]
    exact div_le_div_of_nonneg_right this (by positivity)
  have hHmax : b * a ≤ 2 ^ 900 := by linarith only [hH0hi, hFWhi]
  have hPmax : b * p + q * a ≤ 2 ^ 900 := by
    linarith only [hP1, hbF, hP2, hP2', hH0hi, hFWhi]
  obtain ⟨h1, h2, herr, hlow, -⟩ := mulDD_spec hF xph xpl wh wl hph hpl hwh hwl (b * a) (b * p)
    (q * a) (q * p) (le_of_eq (by rw [ha, hb])) (le_of_eq (by rw [hpd, hb]))
    (le_of_eq (by rw [hq, ha])) (le_of_eq (by rw [hq, hpd])) hHmax hPmax
  rw [← hPV, ← hWV] at herr
  have htiny : (1 : ℝ) / 2 ^ 1070 ≤ (|F| * |W|) / 2 ^ 170 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith only [hlo]
  refine ⟨h1, h2, ?_, ?_⟩
  · have hEm : q * p + (4 * (b * p + q * a) + b * a / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1070 ≤
        (|F| * |W|) / 2 ^ 87 := by
      linarith only [hL2, hL2', hP1, hbF, hP2, hP2', hH0hi, htiny, hFW0]
    have hWVb : |WV| ≤ |W| * (1 + 1 / 2 ^ 80) := by
      have h5 := abs_sub_abs_le_abs_sub WV W
      have h6 := mul_le_mul_of_nonneg_right hθ hW0
      linarith only [h5, h6, hWc]
    have e1 : |PV - F| * |WV| ≤ (η * |F|) * (|W| * (1 + 1 / 2 ^ 80)) :=
      mul_le_mul hP hWVb (abs_nonneg _) (mul_nonneg hη0 hF0)
    have e2 : |F| * |WV - W| ≤ |F| * (θ * |W|) := mul_le_mul_of_nonneg_left hWc hF0
    have e3 : |PV * WV - F * W| ≤ |PV - F| * |WV| + |F| * |WV - W| := by
      rw [show PV * WV - F * W = (PV - F) * WV + F * (WV - W) by ring, ← abs_mul, ← abs_mul]
      exact abs_add_le _ _
    have e4 : η * (|F| * |W|) ≤ 1 / 2 ^ 80 * (|F| * |W|) := mul_le_mul_of_nonneg_right hη hFW0
    have e5 := abs_add_le
      (value (mulDD xph xpl wh wl).1.toBits + value (mulDD xph xpl wh wl).2.toBits - PV * WV)
      (PV * WV - F * W)
    rw [show value (mulDD xph xpl wh wl).1.toBits + value (mulDD xph xpl wh wl).2.toBits -
        PV * WV + (PV * WV - F * W) =
        value (mulDD xph xpl wh wl).1.toBits + value (mulDD xph xpl wh wl).2.toBits - F * W by
      ring] at e5
    linarith only [e5, herr, hEm, e3, e1, e2, e4, hFW0]
  · have hm := fapprox_mul (fapprox_self wh hwh) (fapprox_self xph hph) b a (le_of_eq hb.symm)
      (le_of_eq ha.symm) (b * a) (by simp) (by linarith only [hHmax])
    have hv1 : b * a * (1 - 1 / 2 ^ 53) - 1 / 2 ^ 1075 ≤ |value (mulDD xph xpl wh wl).1.toBits| := by
      have h := hm.2
      have h' := abs_sub_abs_le_abs_sub (value wh.toBits * value xph.toBits)
        (value (wh * xph).toBits)
      rw [abs_mul, ← ha, ← hb, abs_sub_comm] at h'
      show b * a * (1 - 1 / 2 ^ 53) - 1 / 2 ^ 1075 ≤ |value (wh * xph).toBits|
      simp only [zero_mul, mul_zero, add_zero, zero_add] at h
      linarith only [h, h']
    have hv1' := mul_le_mul_of_nonneg_left hv1
      (add_nonneg hκ0 (by positivity) : (0 : ℝ) ≤ κ + 1 / 2 ^ 46)
    have hbalo : 1 / 2 ^ 1000 ≤ b * a := by
      have := mul_le_mul_of_nonneg_right hlo
        (by norm_num : (0 : ℝ) ≤ (1 - 1 / 2 ^ 47) * (1 - 1 / 2 ^ 39))
      linarith only [this, hH0lo]
    have hκba : 0 ≤ κ * b * a := mul_nonneg (mul_nonneg hκ0 hb0) ha0
    linarith only [hlow, hP1, hbF', hP2, hP2', hv1', hbalo, hκ, hκ0, hκba]

/-- `W x n = x (x + 1) ⋯ (x + n)`. -/
noncomputable def W (x : ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range (n + 1), (x + j)

theorem W_succ (x : ℝ) (n : ℕ) : W x (n + 1) = (x + (n + 1 : ℕ)) * W x n := by
  unfold W
  rw [Finset.prod_range_succ]
  ring

theorem W_lower (x : ℝ) (hgap : ∀ k : ℕ, 1 / 2 ^ 54 ≤ |x + k|) (n : ℕ) :
    (1 / 2 ^ 54) ^ (n + 1) ≤ |W x n| := by
  induction n with
  | zero => simpa [W] using hgap 0
  | succ n ih =>
    rw [W_succ, abs_mul, pow_succ]
    exact (mul_le_mul ih (hgap (n + 1)) (by positivity) (abs_nonneg _)).trans
      (le_of_eq (mul_comm _ _))

theorem W_upper (x : ℝ) (n : ℕ) (hx : ∀ k : ℕ, k ≤ n → |x + k| ≤ 4) : |W x n| ≤ 4 ^ (n + 1) := by
  induction n with
  | zero => simpa [W] using hx 0 le_rfl
  | succ n ih =>
    rw [W_succ, abs_mul, pow_succ]
    exact (le_of_eq (mul_comm _ _)).trans (mul_le_mul (ih fun k hk => hx k (by omega))
      (hx (n + 1) le_rfl) (abs_nonneg _) (by positivity))

/-- The loop body of the shift loop. -/
def body (s : Float × Float × Float × Float) : Float × Float × Float × Float :=
  let (wh, wl, xph, xpl) := s
  let (xph, l) := if xph.abs > 1.0 then fastTwoSum xph 1.0 else fastTwoSum 1.0 xph
  let xpl := xpl + l
  let (wh, wl) := mulDD xph xpl wh wl
  (wh, wl, xph, xpl)

theorem body_eq (wh wl xph xpl : Float) :
    body (wh, wl, xph, xpl) =
      ((mulDD (shiftHi xph).1 (xpl + (shiftHi xph).2) wh wl).1,
        (mulDD (shiftHi xph).1 (xpl + (shiftHi xph).2) wh wl).2, (shiftHi xph).1,
        xpl + (shiftHi xph).2) := rfl

/-- **The shift loop** after `n ≤ 6` steps, for `x` at least `2 ^ -54` from every integer. -/
theorem loop_inv (hF : FmaSpec.FmaNearest) (x : Float) (hx : Finite x.toBits)
    (h1 : -3 < value x.toBits) (hgap : ∀ k : ℕ, 1 / 2 ^ 54 ≤ |value x.toBits + k|) (n : ℕ)
    (hn : n ≤ 6) (hxn : value x.toBits + n ≤ 7 / 2) :
    Finite (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
        fun _ s => body s).1.toBits ∧
      Finite (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
        fun _ s => body s).2.1.toBits ∧
      Finite (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
        fun _ s => body s).2.2.1.toBits ∧
      Finite (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
        fun _ s => body s).2.2.2.toBits ∧
      |value (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
          fun _ s => body s).1.toBits +
        value (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
          fun _ s => body s).2.1.toBits - W (value x.toBits) n| ≤
        n / 2 ^ 83 * |W (value x.toBits) n| ∧
      |value (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
          fun _ s => body s).2.1.toBits| ≤
        n / 2 ^ 46 * |value (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
          fun _ s => body s).1.toBits| ∧
      |value (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
          fun _ s => body s).2.2.1.toBits +
        value (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
          fun _ s => body s).2.2.2.toBits - (value x.toBits + n)| ≤
        n / 2 ^ 98 * |value x.toBits + n| ∧
      |value (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
          fun _ s => body s).2.2.2.toBits| ≤ |value x.toBits + n| / 2 ^ 48 ∧
      (value x.toBits + n < 0 →
        value (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
          fun _ s => body s).2.2.2.toBits = 0 ∧
        value (LeanExe.loop (UInt64.ofNat n) (x, (0.0 : Float), x, (0.0 : Float))
          fun _ s => body s).2.2.1.toBits = value x.toBits + n) := by
  induction n with
  | zero =>
    rw [show UInt64.ofNat 0 = 0 from rfl, loop_zero]
    dsimp only
    refine ⟨hx, zero_finite, hx, zero_finite, ?_, ?_, ?_, ?_, ?_⟩
    · simp [W, zero_value]
    · simp [zero_value]
    · simp [zero_value]
    · rw [zero_value, abs_zero]
      positivity
    · intro _
      simp [zero_value]
  | succ m ih =>
    obtain ⟨hwf, hlf, hpf, hqf, hW, hk, hP, hp, hneg⟩ := ih (by omega) (by push_cast at hxn; linarith)
    rw [loop_succ m (by omega)]
    obtain ⟨S, hS⟩ : ∃ S, S = LeanExe.loop (UInt64.ofNat m) (x, (0.0 : Float), x, (0.0 : Float))
        fun _ s => body s := ⟨_, rfl⟩
    rw [← hS] at hwf hlf hpf hqf hW hk hP hp hneg ⊢
    obtain ⟨wh, wl, xph, xpl⟩ := S
    dsimp only at hwf hlf hpf hqf hW hk hP hp hneg ⊢
    rw [body_eq]
    dsimp only
    set vx := value x.toBits with hvx
    have hm6 : (m : ℝ) ≤ 5 := by exact_mod_cast (show m ≤ 5 by omega)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hxn ⊢
    have hgm := hgap m
    have hgm1 := hgap (m + 1)
    push_cast at hgm1
    rw [show vx + (m + 1) = vx + m + 1 by ring] at hgm1
    have hF0 : vx + m ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hgm
      linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 54)]
    obtain ⟨hs1, hs2, hsr, hsl, hsn⟩ := shift_step xph xpl hpf hqf (vx + m) (m / 2 ^ 98)
      hP hp hneg hF0 (by linarith) (by linarith) (by positivity) (by linarith)
    have hWlo := W_lower vx hgap m
    have hWhi := W_upper vx m (fun k hk => by
      have : (k : ℝ) ≤ m := by exact_mod_cast hk
      have := Nat.cast_nonneg (α := ℝ) k
      rw [abs_le]
      constructor <;> linarith)
    have hlo : 1 / 2 ^ 900 ≤ |vx + m + 1| * |W vx m| := by
      have h7 : (1 / 2 ^ 54 : ℝ) ^ (m + 1) ≥ (1 / 2 ^ 54) ^ 7 :=
        pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
      have := mul_le_mul hgm1 (le_trans h7 hWlo) (by positivity) (abs_nonneg _)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 900 ≤ 1 / 2 ^ 54 * (1 / 2 ^ 54) ^ 7)]
    obtain ⟨hp1, hp2, hpe, hpk⟩ := prod_step hF (shiftHi xph).1 (xpl + (shiftHi xph).2)
      wh wl hs1 hs2 hwf hlf (vx + m + 1) (W vx m) (m / 2 ^ 98 + 1 / 2 ^ 98) (m / 2 ^ 83)
      (m / 2 ^ 46) hsr hsl hW hk (by positivity) (by linarith) (by linarith) (by positivity)
      (by linarith)
      hlo (abs_le.mpr ⟨by linarith, by linarith⟩)
      (hWhi.trans (by
        calc (4 : ℝ) ^ (m + 1) ≤ 4 ^ 7 := pow_le_pow_right₀ (by norm_num) (by omega)
          _ ≤ 2 ^ 100 := by norm_num))
    have hWs : W vx (m + 1) = (vx + m + 1) * W vx m := by
      rw [W_succ]; push_cast; ring
    refine ⟨hp1, hp2, hs1, hs2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hWs, abs_mul]
      refine hpe.trans ?_
      have : m / 2 ^ 98 + 1 / 2 ^ 98 + m / 2 ^ 83 + 1 / 2 ^ 84 ≤ ((m : ℝ) + 1) / 2 ^ 83 := by
        linarith
      exact mul_le_mul_of_nonneg_right this (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · refine hpk.trans (le_of_eq ?_)
      ring
    · rw [show vx + m + 1 = vx + (m + 1) by ring] at hsr
      refine hsr.trans (le_of_eq ?_)
      ring
    · rw [show vx + m + 1 = vx + (m + 1) by ring] at hsl
      exact hsl
    · intro h
      obtain ⟨h1', h2'⟩ := hsn (by linarith)
      exact ⟨h1', by rw [h2']; ring⟩

#print axioms shift_step
#print axioms mag_bounds
#print axioms prod_step
#print axioms loop_inv

end Verified.Examples.TgammaMainLoop
