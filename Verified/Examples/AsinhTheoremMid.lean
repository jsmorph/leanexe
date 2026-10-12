import Verified.Examples.AsinhTheoremLarge
import LeanExe.ProofKit.F64RelError

/-!
The middle branch of `Asinh.asinh`, `2 ≤ |x| < 2 ^ 29`: the code computes
`z = 2 |x| + 1/(√(x² + 1) + |x|)`, whose exact value is `|x| + √(x² + 1)`, with a relative error
below `1.32 · 2 ^ -53` (`F64RelError`).  Then `log z` lies within `2 ^ -52` of `arsinh |x|`, both
are at least 1, and `F64Compose.within_two_of_close` turns the one step of `Log.log z` into two
steps against `arsinh |x|`.
-/

namespace Verified.Examples.AsinhTheoremMid
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RelError AtanTheoremBranches
  AsinhTheoremBranches

set_option exponentiation.threshold 4096

/-- `log` moves by at most `ρ/(1 - ρ)` under a relative error `ρ`. -/
theorem log_close (u v ρ : ℝ) (hv : 0 < v) (hρ1 : ρ < 1) (h : |u - v| ≤ ρ * v) :
    |Real.log u - Real.log v| ≤ ρ / (1 - ρ) := by
  have h' := abs_le.mp h
  have hρ0 : 0 ≤ ρ := by
    by_contra hc
    push Not at hc
    have := (abs_nonneg (u - v)).trans h
    nlinarith
  have hu : 0 < u := by nlinarith
  have hq : 0 < u / v := div_pos hu hv
  have hlog : Real.log u - Real.log v = Real.log (u / v) := (Real.log_div hu.ne' hv.ne').symm
  rw [hlog, abs_le]
  have hd : 0 < 1 - ρ := by linarith
  constructor
  · have h3 := Real.one_sub_inv_le_log_of_pos hq
    have h4 : (u / v)⁻¹ ≤ 1 / (1 - ρ) := by
      rw [inv_div, div_le_div_iff₀ hu hd]
      nlinarith
    have h5 : 1 - 1 / (1 - ρ) = -(ρ / (1 - ρ)) := by field_simp; ring
    linarith
  · have h3 := Real.log_le_sub_one_of_pos hq
    have h4 : u / v - 1 ≤ ρ := by
      rw [div_sub_one hv.ne', div_le_iff₀ hv]
      linarith
    have h5 : ρ ≤ ρ / (1 - ρ) := by
      rw [le_div_iff₀ hd]
      nlinarith
    linarith

theorem one_bits : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl

theorem one_rapprox : RApprox (1.0 : Float).toBits 1 0 := by
  rw [one_bits]
  have hv : value (0x3FF0000000000000 : UInt64) = 1 := by
    rw [AtanTheoremCases.word_eq 0x3FF0000000000000 1 (by decide +kernel)]
    norm_num
  have h := rapprox_self (0x3FF0000000000000 : UInt64)
    (by unfold CodeLib.IEEE64.Finite; decide) (by rw [hv]; norm_num)
  rwa [hv] at h

theorem arsinh_ge (a : ℝ) (ha : 2 ≤ a) : 5 / 4 ≤ Real.arsinh a := by
  have hs : a ≤ Real.sqrt (1 + a ^ 2) :=
    (Real.le_sqrt (by linarith) (by positivity)).mpr (by nlinarith)
  have h4 : Real.log 4 ≤ Real.arsinh a :=
    Real.log_le_log (by norm_num) (by linarith)
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h4
  have hl := Real.log_two_gt_d9
  norm_num at hl h4 ⊢
  linarith

/-- `2 ≤ |x| ≤ 2 ^ 29`, before the sign. -/
theorem asinh_mid_w (x : Float) (hx : Finite x.toBits) (h2 : 2 ≤ |value x.toBits|)
    (h29 : |value x.toBits| ≤ 2 ^ 29) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log.log (2.0 * x.abs + 1.0 / ((x * x + 1.0).sqrt + x.abs))).toBits := by
  set a := |value x.toBits| with ha
  have ha0 : 0 < a := by linarith
  obtain ⟨haf, hav⟩ := AtanTheoremReduce.abs_facts x hx
  have hA : RApprox x.abs.toBits a 0 := by
    have h := rapprox_self x.abs.toBits haf (by rw [hav]; exact ha0)
    rwa [hav] at h
  -- `x * x`
  have hxx : RApprox (x * x).toBits (a * a) (1001 / 1000 / 2 ^ 53) := by
    have h58 : a * a ≤ 2 ^ 29 * 2 ^ 29 := mul_le_mul h29 h29 ha0.le (by positivity)
    have hmul := approx_mul (approx_self x.toBits hx) (approx_self x.toBits hx) a a
      le_rfl le_rfl (a * a) (le_of_eq (by ring)) (by norm_num at h58 ⊢; linarith)
    rw [← F64Bits.toBits_mul] at hmul
    refine ⟨mul_pos ha0 ha0, ?_⟩
    have hsq : value x.toBits * value x.toBits = a * a := by
      rw [ha, ← abs_mul, abs_mul_self]
    rw [hsq] at hmul
    refine hmul.mono ?_
    have h4 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 1000 / 2 ^ 53 * (a * a) := by
      have : (4 : ℝ) ≤ a * a := by nlinarith
      have h5 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 1000 / 2 ^ 53 * 4 := by norm_num
      nlinarith
    nlinarith
  -- `x * x + 1`
  have ht2 := (rapprox_add hxx one_rapprox (1001 / 1000 / 2 ^ 53) (by nlinarith)
    (by nlinarith)).mono (ρ' := 2002 / 1000 / 2 ^ 53) (by norm_num)
  rw [← F64Bits.toBits_add] at ht2
  -- the square root
  have ht3 := (rapprox_sqrt ht2 (by norm_num)).mono (ρ' := 3003 / 1000 / 2 ^ 53) (by norm_num)
  rw [← F64Bits.toBits_sqrt] at ht3
  set r := Real.sqrt (a * a + 1) with hr
  have hra : a ≤ r := by
    rw [hr]
    exact (Real.le_sqrt ha0.le (by positivity)).mpr (by nlinarith)
  have hrsq : r * r = a * a + 1 := Real.mul_self_sqrt (by positivity)
  -- `√(x² + 1) + |x|`
  have ht4 := (rapprox_add ht3 hA (3003 / 1000 / 2 ^ 53) (by nlinarith) (by nlinarith)).mono
    (ρ' := 4004 / 1000 / 2 ^ 53) (by norm_num)
  rw [← F64Bits.toBits_add] at ht4
  -- `1/(√(x² + 1) + |x|)`
  have hden : 2 * a ≤ r + a := by linarith
  have hq0 : 0 < 1 / (r + a) := by positivity
  have hr1 : r ≤ a + 1 := by
    rw [hr, Real.sqrt_le_left (by linarith)]
    nlinarith
  have ht5 := (rapprox_div one_rapprox ht4 (by norm_num) (1 / 2 ^ 1040)
    (by
      have h3 : 1 / 2 ^ 31 ≤ 1 / (r + a) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h5 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1040 * (1 / 2 ^ 31) := by norm_num
      have h6 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 1040)
      linarith)
    (by
      have h3 : 1 / (r + a) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have h4 : (1 + 0) / (1 - 4004 / 1000 / 2 ^ 53 : ℝ) ≤ 2 := by norm_num
      nlinarith)).mono (ρ' := 5006 / 1000 / 2 ^ 53) (by norm_num)
  rw [← F64Bits.toBits_div] at ht5
  -- `2 |x|`
  obtain ⟨h2f, h2v⟩ := AtanTheoremReduce.double_float x.abs haf
    (by rw [hav, abs_abs]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 2)])
    (by rw [hav, abs_abs]; linarith [(by norm_num : (2 : ℝ) ^ 29 < 2 ^ 900)])
  have h2a : RApprox (2.0 * x.abs).toBits (2 * a) 0 := by
    have h := rapprox_self _ h2f (by rw [h2v, hav]; linarith)
    rwa [h2v, hav] at h
  -- the argument `z`
  have hq1 : 1 / (r + a) ≤ 1 / (2 * a) :=
    one_div_le_one_div_of_le (by positivity) hden
  have hq2 : 1 / (2 * a) ≤ 2 * a / 15 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hz := (rapprox_add h2a ht5 (314 / 1000 / 2 ^ 53) (by linarith) (by linarith)).mono
    (ρ' := 1315 / 1000 / 2 ^ 53) (by norm_num)
  rw [← F64Bits.toBits_add] at hz
  have hzv : 2 * a + 1 / (r + a) = a + Real.sqrt (1 + a ^ 2) := by
    have hr' : Real.sqrt (1 + a ^ 2) = r := by rw [hr]; congr 1; ring
    have hne : r + a ≠ 0 := (by linarith : (0 : ℝ) < r + a).ne'
    have hinv : 1 / (r + a) = r - a := by
      rw [div_eq_iff hne]
      nlinarith [hrsq]
    rw [hr', hinv]
    ring
  rw [hzv] at hz
  set w := 2.0 * x.abs + 1.0 / ((x * x + 1.0).sqrt + x.abs) with hw
  have hwpos : 0 < value w.toBits := by
    have := hz.bounds.1
    have : (0 : ℝ) < a + Real.sqrt (1 + a ^ 2) := by positivity
    nlinarith
  have hlog := LogTheorem.log_within_one w hz.2.1 hwpos
  have hcl := log_close (value w.toBits) (a + Real.sqrt (1 + a ^ 2)) (1315 / 1000 / 2 ^ 53)
    (by positivity) (by norm_num) hz.2.2
  have hy2 := arsinh_ge a h2
  have hB := F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)
  have hB1 : value (UInt64.ofNat (1023 * 2 ^ 52)) = 1 := by rw [hB]; norm_num
  have hy1 : 1 ≤ Real.log (value w.toBits) := by
    have h3 : (1315 / 1000 / 2 ^ 53 : ℝ) / (1 - 1315 / 1000 / 2 ^ 53) ≤ 1 / 4 := by
      norm_num
    rw [Real.arsinh] at hy2
    have := (abs_le.mp hcl).1
    linarith
  have hyt : Real.arsinh a ≤ 2 ^ 30 := by
    have h3 : Real.arsinh a ≤ a + Real.sqrt (1 + a ^ 2) - 1 := by
      rw [Real.arsinh]
      exact Real.log_le_sub_one_of_pos (by positivity)
    have h4 : Real.sqrt (1 + a ^ 2) ≤ a + 1 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith
  refine F64Compose.within_two_of_close _ _ _ hlog 1023 (by norm_num) (by norm_num)
    (by rw [hB1]; exact hy1) (by rw [hB1]; linarith) ?_ ?_ ?_
  · rw [Real.arsinh]
    have h3 : (1315 / 1000 / 2 ^ 53 : ℝ) / (1 - 1315 / 1000 / 2 ^ 53) < (2 : ℝ) ^ (1023 - 1) / 2 ^ 1074 := by
      norm_num
    exact lt_of_le_of_lt hcl h3
  · rw [show F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - 2 ^ 970 from rfl]
    have := (abs_le.mp hcl).2
    have h3 : (1315 / 1000 / 2 ^ 53 : ℝ) / (1 - 1315 / 1000 / 2 ^ 53) ≤ 1 := by norm_num
    rw [Real.arsinh] at hyt
    linarith [(by norm_num : (2 : ℝ) ^ 30 + 1 < 2 ^ 1024 - 2 ^ 970)]
  · rw [show F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - 2 ^ 970 from rfl]
    linarith [(by norm_num : (2 : ℝ) ^ 30 < 2 ^ 1024 - 2 ^ 970)]

#print axioms asinh_mid_w

end Verified.Examples.AsinhTheoremMid
