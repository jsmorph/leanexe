import Verified.Examples.TgammaRefl1

/-!
The quotient `π/(lh + ll)` of the path of `tgammaWith` below `-3`, as the double-double
`rh = (1/lh) p1` and `rl = (1/lh) (p2 - ll rh - fma rh lh (-p1))` with `P = p1 + p2`.  With
`D = lh + ll`, the exact correction is `c = P - rh D = p2 - ll rh - (rh lh - p1)`, so that
`rh + c/D = P/D`.  `pi_head` bounds `1/lh` and `rh` relative to `R = 1/|lh|`, `pi_tail` the
computed `c`, and `pi_real` the sum, so that `rh + rl` lies within `2 ^ -68` of `P/D` relative for
`|ll| ≤ 2 ^ -36 |lh|` (`pi_div`).
-/

namespace Verified.Examples.TgammaRefl2
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaFloor

set_option exponentiation.threshold 4096

/-- `1/lh` and `rh = (1/lh) p1` in units of `R = 1/|lh|`. -/
theorem pi_head (lh p1 : Float) (hlh : Finite lh.toBits) (hp1 : Finite p1.toBits)
    (hlo : 1 / 2 ^ 53 ≤ |value lh.toBits|) (hhi : |value lh.toBits| ≤ 3)
    (hp1v : |value p1.toBits| ≤ 4) :
    Finite (1.0 / lh).toBits ∧ Finite ((1.0 / lh) * p1).toBits ∧
      |value (1.0 / lh).toBits - 1 / value lh.toBits| ≤ 1 / |value lh.toBits| / 2 ^ 52 ∧
      |value ((1.0 / lh) * p1).toBits - value p1.toBits / value lh.toBits| ≤
        1 / |value lh.toBits| / 2 ^ 49 := by
  have hl0 : 0 < |value lh.toBits| := lt_of_lt_of_le (by positivity) hlo
  obtain ⟨R, hR⟩ : ∃ R, R = 1 / |value lh.toBits| := ⟨_, rfl⟩
  rw [← hR]
  have hR0 : 0 < R := by rw [hR]; positivity
  have hR3 : 1 / 3 ≤ R := by
    rw [hR]
    exact one_div_le_one_div_of_le hl0 hhi
  have hR53 : R ≤ 2 ^ 53 := by
    rw [hR, div_le_iff₀ hl0]
    have := mul_le_mul_of_nonneg_left hlo (by positivity : (0 : ℝ) ≤ 2 ^ 53)
    linarith [(by norm_num : (2 : ℝ) ^ 53 * (1 / 2 ^ 53) = 1)]
  have hq := fapprox_div (fapprox_self 1.0 TgammaRecip.one_finite) (fapprox_self lh hlh) 1
    |value lh.toBits| (by rw [TgammaRecip.one_value, abs_one]) le_rfl hl0 R
    (by rw [add_zero, sub_zero, hR]) (by linarith [(by norm_num : (2 : ℝ) ^ 53 < 2 ^ 1022)])
  rw [TgammaRecip.one_value] at hq
  have hVa : |1 / value lh.toBits| = R := by rw [abs_div, abs_one, hR]
  have hq2 : FApprox (1.0 / lh) (1 / value lh.toBits) (R / 2 ^ 52) := by
    refine Approx.mono hq ?_
    simp only [mul_zero, zero_div, add_zero, sub_zero, zero_add]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 3 / 2 ^ 53)]
  have hh := fapprox_mul hq2 (fapprox_self p1 hp1) R 4 hVa.le hp1v (R * (1 + 1 / 2 ^ 52) * 4)
    (le_of_eq (by ring)) (by nlinarith [(by norm_num : (2 : ℝ) ^ 53 * (1 + 1 / 2 ^ 52) * 4 < 2 ^ 1022)])
  refine ⟨hq2.1, hh.1, hq2.2, ?_⟩
  have h2 := hh.2
  rw [show 1 / value lh.toBits * value p1.toBits = value p1.toBits / value lh.toBits by ring] at h2
  simp only [mul_zero, add_zero] at h2
  linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 3 / 2 ^ 53)]

/-- The computed correction `p2 - ll rh - fma rh lh (-p1)`. -/
theorem pi_tail (hF : FmaSpec.FmaNearest) (lh ll p1 p2 rh : Float) (hlh : Finite lh.toBits)
    (hll : Finite ll.toBits) (hp1 : Finite p1.toBits) (hp2 : Finite p2.toBits)
    (hrh : Finite rh.toBits) (hr : |value rh.toBits * value lh.toBits - value p1.toBits| ≤ 1 / 2 ^ 49)
    (hm : |value ll.toBits * value rh.toBits| ≤ 1 / 2 ^ 33) (hp2v : |value p2.toBits| ≤ 1 / 2 ^ 52) :
    Finite (p2 - ll * rh - Fma.fma rh lh (-p1)).toBits ∧
      |value (p2 - ll * rh - Fma.fma rh lh (-p1)).toBits -
          (value p2.toBits - value ll.toBits * value rh.toBits -
            (value rh.toBits * value lh.toBits - value p1.toBits))| ≤ 1 / 2 ^ 82 ∧
      |value (p2 - ll * rh - Fma.fma rh lh (-p1)).toBits| ≤ 1 / 2 ^ 31 := by
  obtain ⟨hnf, hnv⟩ := neg_float p1 hp1
  have hf := fma_approx hF rh lh (-p1) hrh hlh hnf
    (by rw [hnv, ← sub_eq_add_neg]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 49 ≤ 2 ^ 1000)])
  rw [hnv, ← sub_eq_add_neg] at hf
  have hf' : FApprox (Fma.fma rh lh (-p1)) (value rh.toBits * value lh.toBits - value p1.toBits)
      (1 / 2 ^ 100) := Approx.mono hf (by
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 49 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 100)])
  have hmA := fapprox_mul (fapprox_self ll hll) (fapprox_self rh hrh) |value ll.toBits|
    |value rh.toBits| le_rfl le_rfl (|value ll.toBits| * |value rh.toBits|) (by simp)
    (by rw [← abs_mul]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 33 < 2 ^ 1022)])
  have hm' : FApprox (ll * rh) (value ll.toBits * value rh.toBits) (1 / 2 ^ 85) :=
    Approx.mono hmA (by
      simp only [zero_mul, mul_zero, add_zero, zero_add]
      rw [← abs_mul]
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 33 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 85)])
  have ha := fapprox_sub (fapprox_self p2 hp2) hm' (1 / 2 ^ 32)
    (by linarith [abs_sub (value p2.toBits) (value ll.toBits * value rh.toBits),
      (by norm_num : (1 : ℝ) / 2 ^ 52 + 1 / 2 ^ 33 + (0 + 1 / 2 ^ 85) ≤ 1 / 2 ^ 32)])
    (by norm_num)
  have hs1 := abs_sub (value p2.toBits - value ll.toBits * value rh.toBits)
    (value rh.toBits * value lh.toBits - value p1.toBits)
  have hs2 := abs_sub (value p2.toBits) (value ll.toBits * value rh.toBits)
  have hb := fapprox_sub ha hf' (1 / 2 ^ 31)
    (by linarith [hs1, hs2,
      (by norm_num : (1 : ℝ) / 2 ^ 52 + 1 / 2 ^ 33 + 1 / 2 ^ 49 +
        (0 + 1 / 2 ^ 85 + 1 / 2 ^ 32 / 2 ^ 53 + 1 / 2 ^ 100) ≤ 1 / 2 ^ 31)])
    (by norm_num)
  refine ⟨hb.1, hb.2.trans (by norm_num), ?_⟩
  have := Approx.mag hb
  linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 + 1 / 2 ^ 33 + 1 / 2 ^ 49 +
    (0 + 1 / 2 ^ 85 + 1 / 2 ^ 32 / 2 ^ 53 + 1 / 2 ^ 100 + 1 / 2 ^ 31 / 2 ^ 53) ≤ 1 / 2 ^ 31)]

/-- The real assembly: `rh + rl` within `2 ^ -68` of `P/D` relative. -/
theorem pi_real (vlh vll P vrh vrcp vb vrl R : ℝ) (hR0 : 0 < R) (hR : R * |vlh| = 1)
    (hll : |vll| ≤ |vlh| / 2 ^ 36) (hP1 : 3 ≤ P)
    (hrh : |vrh - P / vlh| ≤ R / 2 ^ 48)
    (hb : |vb - (P - vrh * (vlh + vll))| ≤ 1 / 2 ^ 82) (hbb : |vb| ≤ 1 / 2 ^ 31)
    (hq : |vrcp - 1 / vlh| ≤ R / 2 ^ 52) (hrl : |vrl - vrcp * vb| ≤ R / 2 ^ 82) :
    |vrh + vrl - P / (vlh + vll)| ≤ |P / (vlh + vll)| / 2 ^ 68 ∧ |vrl| ≤ |vrh| / 2 ^ 32 := by
  have hl0 : 0 < |vlh| := by
    rcases (abs_nonneg vlh).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hR; exact absurd hR (by norm_num)
  have hvlh : vlh ≠ 0 := abs_pos.mp hl0
  have hll' : |vll| ≤ |vlh| / 2 ^ 36 := hll
  have hD0 : |vlh| * (1 - 1 / 2 ^ 36) ≤ |vlh + vll| := by
    have := abs_sub_abs_le_abs_sub vlh (-vll)
    rw [sub_neg_eq_add, abs_neg] at this
    linarith
  have hD : 0 < |vlh + vll| := lt_of_lt_of_le (by positivity) hD0
  have hDne : vlh + vll ≠ 0 := abs_pos.mp hD
  obtain ⟨V, hV⟩ : ∃ V, V = 1 / vlh := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 1 / (vlh + vll) := ⟨_, rfl⟩
  have hVa : |V| = R := by
    rw [hV, abs_div, abs_one]
    field_simp
    linarith
  have hWa : |W| * |vlh + vll| = 1 := by
    rw [hW, abs_div, abs_one]
    field_simp
  -- `|W| ≤ R (1 + 2 ^ -35)`
  have hWR : |W| ≤ R * (1 + 1 / 2 ^ 35) := by
    have h1 : |W| * (|vlh| * (1 - 1 / 2 ^ 36)) ≤ |W| * |vlh + vll| :=
      mul_le_mul_of_nonneg_left hD0 (abs_nonneg _)
    rw [hWa] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 hR0.le
    have h3 : |W| * (|vlh| * (1 - 1 / 2 ^ 36)) * R = |W| * (1 - 1 / 2 ^ 36) := by
      rw [show |W| * (|vlh| * (1 - 1 / 2 ^ 36)) * R = |W| * (1 - 1 / 2 ^ 36) * (R * |vlh|) by ring,
        hR, mul_one]
    rw [h3, one_mul] at h2
    linarith [abs_nonneg W]
  have hPD : P / (vlh + vll) = P * W := by rw [hW]; ring
  have hPV : P / vlh = P * V := by rw [hV]; ring
  rw [hPD]
  rw [hPV] at hrh
  rw [← hV] at hq
  -- `P W - rh = c W` with `c = P - rh D`
  have hc : P * W - vrh = (P - vrh * (vlh + vll)) * W := by
    rw [sub_mul, mul_assoc, show (vlh + vll) * W = 1 by rw [hW]; field_simp, mul_one]
  have hVW : V - W = V * W * vll := by
    rw [hV, hW]; field_simp; ring
  have hcb : |P - vrh * (vlh + vll)| ≤ 1 / 2 ^ 31 + 1 / 2 ^ 82 := by
    have := abs_sub_abs_le_abs_sub (P - vrh * (vlh + vll)) vb
    rw [abs_sub_comm] at hb
    linarith
  have hsplit : vrh + vrl - P * W = (vrl - vrcp * vb) + (vrcp - V) * vb +
      V * (vb - (P - vrh * (vlh + vll))) + (P - vrh * (vlh + vll)) * (V - W) := by
    rw [show (P - vrh * (vlh + vll)) * (V - W) = (P - vrh * (vlh + vll)) * V -
      (P * W - vrh) by rw [hc]; ring]
    ring
  have t1 : |(vrcp - V) * vb| ≤ R / 2 ^ 52 * (1 / 2 ^ 31) := by
    rw [abs_mul]; exact mul_le_mul hq hbb (abs_nonneg _) (by positivity)
  have t2 : |V * (vb - (P - vrh * (vlh + vll)))| ≤ R * (1 / 2 ^ 82) := by
    rw [abs_mul, hVa]; exact mul_le_mul_of_nonneg_left hb hR0.le
  have hVWb : |V - W| ≤ |W| / 2 ^ 36 := by
    rw [hVW, abs_mul, abs_mul, hVa]
    calc R * |W| * |vll| ≤ R * |W| * (|vlh| / 2 ^ 36) :=
          mul_le_mul_of_nonneg_left hll' (by positivity)
      _ = |W| / 2 ^ 36 * (R * |vlh|) := by ring
      _ = |W| / 2 ^ 36 := by rw [hR, mul_one]
  have t3 : |(P - vrh * (vlh + vll)) * (V - W)| ≤ (1 / 2 ^ 31 + 1 / 2 ^ 82) * (|W| / 2 ^ 36) := by
    rw [abs_mul]; exact mul_le_mul hcb hVWb (abs_nonneg _) (by positivity)
  have hWlo : R * (1 - 1 / 2 ^ 35) ≤ |W| := by
    have h1 : |vlh + vll| ≤ |vlh| * (1 + 1 / 2 ^ 36) := by
      have := abs_add_le vlh vll
      linarith
    have h2 : |W| * |vlh + vll| ≤ |W| * (|vlh| * (1 + 1 / 2 ^ 36)) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    rw [hWa] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 hR0.le
    have h4 : |W| * (|vlh| * (1 + 1 / 2 ^ 36)) * R = |W| * (1 + 1 / 2 ^ 36) := by
      rw [show |W| * (|vlh| * (1 + 1 / 2 ^ 36)) * R = |W| * (1 + 1 / 2 ^ 36) * (R * |vlh|) by
        ring, hR, mul_one]
    rw [h4, one_mul] at h3
    linarith [abs_nonneg W]
  have hPW : |P * W| = P * |W| := by rw [abs_mul, abs_of_pos (by linarith)]
  constructor
  · rw [hsplit, hPW]
    have e1 := abs_add_le ((vrl - vrcp * vb) + (vrcp - V) * vb + V * (vb - (P - vrh * (vlh + vll))))
      ((P - vrh * (vlh + vll)) * (V - W))
    have e2 := abs_add_le ((vrl - vrcp * vb) + (vrcp - V) * vb) (V * (vb - (P - vrh * (vlh + vll))))
    have e3 := abs_add_le (vrl - vrcp * vb) ((vrcp - V) * vb)
    have h3W : 3 * |W| ≤ P * |W| := mul_le_mul_of_nonneg_right hP1 (abs_nonneg _)
    linarith
  · have hvrcp : |vrcp| ≤ R * (1 + 1 / 2 ^ 52) := by
      have := abs_sub_abs_le_abs_sub vrcp V
      rw [hVa] at this
      linarith
    have hrl1 : |vrl| ≤ R / 2 ^ 82 + R * (1 + 1 / 2 ^ 52) * (1 / 2 ^ 31) := by
      have := abs_sub_abs_le_abs_sub vrl (vrcp * vb)
      have h2 : |vrcp * vb| ≤ R * (1 + 1 / 2 ^ 52) * (1 / 2 ^ 31) := by
        rw [abs_mul]; exact mul_le_mul hvrcp hbb (abs_nonneg _) (by positivity)
      linarith
    have hrh1 : 3 * R - R / 2 ^ 48 ≤ |vrh| := by
      have := abs_sub_abs_le_abs_sub (P * V) vrh
      rw [abs_sub_comm] at hrh
      have h4 : |P * V| = P * R := by rw [abs_mul, hVa, abs_of_pos (show (0 : ℝ) < P by linarith)]
      have h6 : 3 * R ≤ P * R := mul_le_mul_of_nonneg_right hP1 hR0.le
      linarith
    linarith

/-- **The quotient** `P/(lh + ll)` as `rh + rl`. -/
theorem pi_div (hF : FmaSpec.FmaNearest) (lh ll p1 p2 : Float) (hlh : Finite lh.toBits)
    (hll : Finite ll.toBits) (hp1 : Finite p1.toBits) (hp2 : Finite p2.toBits)
    (hlo : 1 / 2 ^ 53 ≤ |value lh.toBits|) (hhi : |value lh.toBits| ≤ 3)
    (hllb : |value ll.toBits| ≤ |value lh.toBits| / 2 ^ 36)
    (hp1a : 31 / 10 ≤ value p1.toBits) (hp1b : value p1.toBits ≤ 7 / 2)
    (hp2v : |value p2.toBits| ≤ 1 / 2 ^ 52) :
    Finite ((1.0 / lh) * p1).toBits ∧
      Finite ((1.0 / lh) * (p2 - ll * ((1.0 / lh) * p1) - Fma.fma ((1.0 / lh) * p1) lh (-p1))).toBits ∧
      |value ((1.0 / lh) * p1).toBits +
          value ((1.0 / lh) * (p2 - ll * ((1.0 / lh) * p1) -
            Fma.fma ((1.0 / lh) * p1) lh (-p1))).toBits -
          (value p1.toBits + value p2.toBits) / (value lh.toBits + value ll.toBits)| ≤
        |(value p1.toBits + value p2.toBits) / (value lh.toBits + value ll.toBits)| / 2 ^ 68 ∧
      |value ((1.0 / lh) * (p2 - ll * ((1.0 / lh) * p1) -
          Fma.fma ((1.0 / lh) * p1) lh (-p1))).toBits| ≤
        |value ((1.0 / lh) * p1).toBits| / 2 ^ 32 := by
  have hl0 : 0 < |value lh.toBits| := lt_of_lt_of_le (by positivity) hlo
  obtain ⟨hqf, hrhf, hq, hrh⟩ := pi_head lh p1 hlh hp1 hlo hhi
    (abs_le.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨R, hR⟩ : ∃ R, R = 1 / |value lh.toBits| := ⟨_, rfl⟩
  rw [← hR] at hq hrh
  have hR0 : 0 < R := by rw [hR]; positivity
  have hRl : R * |value lh.toBits| = 1 := by rw [hR]; field_simp
  generalize 1.0 / lh = q at hqf hrhf hq hrh ⊢
  generalize q * p1 = rh at hrhf hrh ⊢
  -- `rh lh - p1` and `ll rh`
  have hr1 : |value rh.toBits * value lh.toBits - value p1.toBits| ≤ 1 / 2 ^ 49 := by
    have hlne : value lh.toBits ≠ 0 := abs_pos.mp hl0
    have : value rh.toBits * value lh.toBits - value p1.toBits =
        (value rh.toBits - value p1.toBits / value lh.toBits) * value lh.toBits := by
      rw [sub_mul, div_mul_cancel₀ _ hlne]
    rw [this, abs_mul]
    calc |value rh.toBits - value p1.toBits / value lh.toBits| * |value lh.toBits| ≤
        R / 2 ^ 49 * |value lh.toBits| := mul_le_mul_of_nonneg_right hrh (abs_nonneg _)
      _ = 1 / 2 ^ 49 := by rw [div_mul_eq_mul_div, hRl]
  have hrhm : |value rh.toBits| ≤ R * (4 + 1 / 2 ^ 49) := by
    have h1 := abs_sub_abs_le_abs_sub (value rh.toBits) (value p1.toBits / value lh.toBits)
    have h2 : |value p1.toBits / value lh.toBits| ≤ 4 * R := by
      rw [abs_div, hR, abs_of_pos (by linarith)]
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hm : |value ll.toBits * value rh.toBits| ≤ 1 / 2 ^ 33 := by
    rw [abs_mul]
    calc |value ll.toBits| * |value rh.toBits| ≤
        |value lh.toBits| / 2 ^ 36 * (R * (4 + 1 / 2 ^ 49)) :=
          mul_le_mul hllb hrhm (abs_nonneg _) (by positivity)
      _ = (4 + 1 / 2 ^ 49) / 2 ^ 36 * (R * |value lh.toBits|) := by ring
      _ ≤ 1 / 2 ^ 33 := by rw [hRl]; norm_num
  obtain ⟨hbf, hbe, hbb⟩ := pi_tail hF lh ll p1 p2 rh hlh hll hp1 hp2 hrhf hr1 hm hp2v
  generalize p2 - ll * rh - Fma.fma rh lh (-p1) = b at hbf hbe hbb ⊢
  -- `rl = q b`
  have hRle : R ≤ 2 ^ 53 := by
    rw [hR, div_le_iff₀ hl0]
    have := mul_le_mul_of_nonneg_left hlo (by positivity : (0 : ℝ) ≤ 2 ^ 53)
    linarith [(by norm_num : (2 : ℝ) ^ 53 * (1 / 2 ^ 53) = 1)]
  have hR3 : 1 / 3 ≤ R := by
    rw [hR]
    exact one_div_le_one_div_of_le hl0 hhi
  have hVa : |1 / value lh.toBits| = R := by rw [abs_div, abs_one, hR]
  have hqm : |value q.toBits| ≤ R * (1 + 1 / 2 ^ 52) := by
    have := abs_sub_abs_le_abs_sub (value q.toBits) (1 / value lh.toBits)
    rw [hVa] at this
    linarith
  have hrlA := fapprox_mul (fapprox_self q hqf) (fapprox_self b hbf) (R * (1 + 1 / 2 ^ 52))
    (1 / 2 ^ 31) hqm hbb (R * (1 + 1 / 2 ^ 52) * (1 / 2 ^ 31)) (by simp)
    (by nlinarith [(by norm_num : (2 : ℝ) ^ 53 * (1 + 1 / 2 ^ 52) * (1 / 2 ^ 31) < 2 ^ 1022)])
  have hrl : |value (q * b).toBits - value q.toBits * value b.toBits| ≤ R / 2 ^ 82 := by
    have := hrlA.2
    simp only [zero_mul, mul_zero, add_zero, zero_add] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 3 / 2 ^ 84)]
  have hP := pi_real (value lh.toBits) (value ll.toBits) (value p1.toBits + value p2.toBits)
    (value rh.toBits) (value q.toBits) (value b.toBits) (value (q * b).toBits) R hR0 hRl hllb
    (by linarith [(abs_le.mp hp2v).1])
    (by
      have h1 : (value p1.toBits + value p2.toBits) / value lh.toBits =
          value p1.toBits / value lh.toBits + value p2.toBits / value lh.toBits := by ring
      have h2 : |value p2.toBits / value lh.toBits| ≤ R / 2 ^ 52 := by
        rw [abs_div, hR, div_eq_mul_one_div (|value p2.toBits|)]
        calc |value p2.toBits| * (1 / |value lh.toBits|) ≤ 1 / 2 ^ 52 * (1 / |value lh.toBits|) :=
              mul_le_mul_of_nonneg_right hp2v (by positivity)
          _ = 1 / |value lh.toBits| / 2 ^ 52 := by ring
      rw [h1]
      have := abs_sub_le (value rh.toBits) (value p1.toBits / value lh.toBits)
        (value p1.toBits / value lh.toBits + value p2.toBits / value lh.toBits)
      rw [show value p1.toBits / value lh.toBits -
        (value p1.toBits / value lh.toBits + value p2.toBits / value lh.toBits) =
        -(value p2.toBits / value lh.toBits) by ring, abs_neg] at this
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 49 + 1 / 2 ^ 52 ≤ 1 / 2 ^ 48)])
    (by
      rw [show value p1.toBits + value p2.toBits - value rh.toBits *
        (value lh.toBits + value ll.toBits) = value p2.toBits - value ll.toBits * value rh.toBits -
          (value rh.toBits * value lh.toBits - value p1.toBits) by ring]
      exact hbe)
    hbb hq hrl
  exact ⟨hrhf, hrlA.1, hP.1, hP.2⟩

#print axioms pi_head
#print axioms pi_tail
#print axioms pi_real
#print axioms pi_div

end Verified.Examples.TgammaRefl2
