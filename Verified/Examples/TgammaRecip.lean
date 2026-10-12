import Verified.Examples.TgammaDD

/-!
The reciprocal `fh = 1/x` with the correction `(fma fh (-x) 1) fh` of `tgammaWith` below `1/4`.
The residual `1 - fh x` lies within `2 ^ -52` and is computed by the fused multiply-add, and
`fh + fh (1 - fh x) - 1/x = -(1 - fh x)²/x`, so the pair approximates `1/x` within `2 ^ -100` of
`1/|x|` (`recip_corr`).
-/

namespace Verified.Examples.TgammaRecip
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx TgammaDD

set_option exponentiation.threshold 4096

theorem one_value : value (1.0 : Float).toBits = 1 := by
  rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl, ← PolyBound.ratOfWord_cast,
    show PolyBound.ratOfWord 0x3FF0000000000000 = 1 by decide +kernel]
  norm_num

theorem one_finite : Finite (1.0 : Float).toBits := by
  rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
  unfold CodeLib.IEEE64.Finite
  decide

/-- **The corrected reciprocal** for `2 ^ -900 ≤ |x| ≤ 1/4`. -/
theorem recip_corr (hF : FmaSpec.FmaNearest) (x : Float) (hx : Finite x.toBits)
    (hlo : 1 / 2 ^ 900 ≤ |value x.toBits|) (hhi : |value x.toBits| ≤ 1 / 4) :
    Finite (1.0 / x).toBits ∧ Finite (Fma.fma (1.0 / x) (-x) 1.0 * (1.0 / x)).toBits ∧
      |value (1.0 / x).toBits - 1 / value x.toBits| ≤ |1 / value x.toBits| / 2 ^ 52 ∧
      |value (Fma.fma (1.0 / x) (-x) 1.0 * (1.0 / x)).toBits| ≤ |1 / value x.toBits| / 2 ^ 50 ∧
      |value (1.0 / x).toBits + value (Fma.fma (1.0 / x) (-x) 1.0 * (1.0 / x)).toBits -
          1 / value x.toBits| ≤ |1 / value x.toBits| / 2 ^ 100 := by
  set vx := value x.toBits with hvx
  have hx0 : 0 < |vx| := lt_of_lt_of_le (by positivity) hlo
  have hvx0 : vx ≠ 0 := abs_pos.mp hx0
  set R := |1 / vx| with hR
  have hRv : R = 1 / |vx| := by rw [hR, abs_div, abs_one]
  have hR4 : 4 ≤ R := by
    rw [hRv, le_div_iff₀ hx0]
    linarith
  have hRmax : R ≤ 2 ^ 900 := by
    rw [hRv, div_le_iff₀ hx0]
    calc (1 : ℝ) = 2 ^ 900 * (1 / 2 ^ 900) := by norm_num
      _ ≤ 2 ^ 900 * |vx| := by gcongr
  have hRvx : R * |vx| = 1 := by rw [hRv]; field_simp
  -- `fh = 1/x`
  have hfh0 := fapprox_div (fapprox_self _ one_finite) (fapprox_self x hx) 1 |vx|
    (by rw [one_value, abs_one]) le_rfl hx0 R (by rw [hRv]; simp) (by linarith [(by norm_num : (2 : ℝ) ^ 900 < 2 ^ 1022)])
  rw [one_value] at hfh0
  have htiny : (1 : ℝ) / 2 ^ 1075 ≤ R / 2 ^ 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(by norm_num : (2 : ℝ) ^ 1000 ≤ 4 * 2 ^ 1075)]
  have hfh : FApprox (1.0 / x) (1 / vx) (R / 2 ^ 52) := by
    refine Approx.mono hfh0 ?_
    have : (0 + 1 * 0 / |vx|) / (|vx| - 0) = 0 := by simp
    rw [this, zero_add]
    have h1 : R / 2 ^ 53 + R / 2 ^ 1000 ≤ R / 2 ^ 52 := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [(by norm_num : ((2 : ℝ) ^ 1000 + 2 ^ 53) * 2 ^ 52 ≤ 2 ^ 53 * 2 ^ 1000)]
    linarith
  set fh := 1.0 / x with hfhdef
  set vf := value fh.toBits with hvf
  have hfe : |vf - 1 / vx| ≤ R / 2 ^ 52 := hfh.2
  have hvfb : |vf| ≤ 2 * R := by
    have := abs_sub_abs_le_abs_sub vf (1 / vx)
    have : R / 2 ^ 52 ≤ R := div_le_self (by linarith) (by norm_num)
    linarith
  -- the residual `S = 1 - fh x`
  have hnx := fapprox_neg (fapprox_self x hx)
  have hnxv : value (-x).toBits = -vx := by
    have h0 := abs_nonpos_iff.mp hnx.2
    linarith
  set S := vf * value (-x).toBits + value (1.0 : Float).toBits with hS
  have hSv : S = -vx * (vf - 1 / vx) := by
    rw [hS, hnxv, one_value]
    field_simp
    ring
  have hSb : |S| ≤ 1 / 2 ^ 52 := by
    rw [hSv, abs_mul, abs_neg]
    calc |vx| * |vf - 1 / vx| ≤ |vx| * (R / 2 ^ 52) := mul_le_mul_of_nonneg_left hfe (abs_nonneg _)
      _ = 1 / 2 ^ 52 := by rw [mul_div_assoc', mul_comm, hRvx]
  have hr := fma_approx hF fh (-x) 1.0 hfh.1 hnx.1 one_finite
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 2 ^ 1000)])
  rw [← hS] at hr
  set r := Fma.fma fh (-x) 1.0 with hrdef
  have hre : |value r.toBits - S| ≤ |S| / 2 ^ 53 + 1 / 2 ^ 1075 := hr.2
  -- `corr = r fh`
  have hc0 := fapprox_mul hr (fapprox_self fh hfh.1) (1 / 2 ^ 52) (2 * R) hSb hvfb
    ((1 / 2 ^ 52 + (|S| / 2 ^ 53 + 1 / 2 ^ 1075)) * (2 * R + 0)) le_rfl (by
      have : |S| / 2 ^ 53 ≤ 1 := by
        have : |S| / 2 ^ 53 ≤ |S| := div_le_self (abs_nonneg _) (by norm_num)
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 1)]
      nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 52 + (1 + 1 / 2 ^ 1075) ≤ 3),
        (by norm_num : (3 : ℝ) * (2 * 2 ^ 900) < 2 ^ 1022)])
  set c := r * fh with hcdef
  have hce : |value c.toBits - S * vf| ≤ R / 2 ^ 101 := by
    have h := hc0.2
    have hS0 : 0 ≤ |S| := abs_nonneg _
    have hR0 : 0 ≤ R := by linarith
    -- every term is a small multiple of `R`
    have e1 : (|S| / 2 ^ 53 + 1 / 2 ^ 1075) * (2 * R) ≤ R / 2 ^ 103 := by
      have : |S| / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 104 := by
        have : |S| / 2 ^ 53 ≤ 1 / 2 ^ 105 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 105 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 104)]
      nlinarith
    have e3 : (1 / 2 ^ 52 + (|S| / 2 ^ 53 + 1 / 2 ^ 1075)) * (2 * R + 0) / 2 ^ 53 ≤ R / 2 ^ 103 := by
      have : |S| / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 104 := by
        have : |S| / 2 ^ 53 ≤ 1 / 2 ^ 105 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 105 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 104)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have e4 : (1 : ℝ) / 2 ^ 1075 ≤ R / 2 ^ 1000 := htiny
    have e5 : R / 2 ^ 103 + R / 2 ^ 103 + R / 2 ^ 1000 ≤ R / 2 ^ 101 := by
      have : R / 2 ^ 1000 ≤ R / 2 ^ 103 := div_le_div_of_nonneg_left hR0 (by positivity) (by norm_num)
      linarith
    have : (|S| / 2 ^ 53 + 1 / 2 ^ 1075) * (2 * R) + 1 / 2 ^ 52 * 0 +
        (|S| / 2 ^ 53 + 1 / 2 ^ 1075) * 0 +
        (1 / 2 ^ 52 + (|S| / 2 ^ 53 + 1 / 2 ^ 1075)) * (2 * R + 0) / 2 ^ 53 + 1 / 2 ^ 1075 ≤
        R / 2 ^ 101 := by
      simp only [mul_zero, add_zero]
      linarith
    exact h.trans this
  refine ⟨hfh.1, hc0.1, hfe, ?_, ?_⟩
  · -- `|corr| ≤ R/2^50`
    have h1 := abs_sub_abs_le_abs_sub (value c.toBits) (S * vf)
    have h2 : |S * vf| ≤ 2 * R / 2 ^ 52 := by
      rw [abs_mul]
      calc |S| * |vf| ≤ 1 / 2 ^ 52 * (2 * R) := mul_le_mul hSb hvfb (abs_nonneg _) (by positivity)
        _ = 2 * R / 2 ^ 52 := by ring
    have hR0 : 0 ≤ R := by linarith
    have : R / 2 ^ 101 + 2 * R / 2 ^ 52 ≤ R / 2 ^ 50 := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [(by norm_num : ((2 : ℝ) ^ 52 + 2 * 2 ^ 101) * 2 ^ 50 ≤ 2 ^ 101 * 2 ^ 52)]
    linarith
  · -- `fh + corr - 1/x = -S²/x + (corr - S fh)`
    have hid : vf + S * vf - 1 / vx = -(S ^ 2) / vx := by
      rw [hSv]
      field_simp
      ring
    have hS2 : |-(S ^ 2) / vx| ≤ R / 2 ^ 104 := by
      rw [abs_div, abs_neg, abs_pow]
      have h2 : |S| ^ 2 ≤ 1 / 2 ^ 104 := by
        calc |S| ^ 2 ≤ (1 / 2 ^ 52) ^ 2 := pow_le_pow_left₀ (abs_nonneg S) hSb 2
          _ = 1 / 2 ^ 104 := by norm_num
      rw [div_le_iff₀ hx0]
      calc |S| ^ 2 ≤ 1 / 2 ^ 104 := h2
        _ = R / 2 ^ 104 * |vx| := by rw [div_mul_eq_mul_div, hRvx]
    rw [show vf + value c.toBits - 1 / vx = (vf + S * vf - 1 / vx) + (value c.toBits - S * vf) by ring,
      hid]
    have hR0 : 0 ≤ R := by linarith
    have : R / 2 ^ 104 + R / 2 ^ 101 ≤ R / 2 ^ 100 := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [(by norm_num : ((2 : ℝ) ^ 101 + 2 ^ 104) * 2 ^ 100 ≤ 2 ^ 104 * 2 ^ 101)]
    exact (abs_add_le _ _).trans (by linarith)

#print axioms recip_corr

end Verified.Examples.TgammaRecip
