import Library.Numerics.Float64.Asinh.AsinhTheoremMid

/-!
The middle branch of `Asinh.acosh`, `2 ≤ x ≤ 2 ^ 28`: the code computes
`z = 2 x - 1/(x + √(x² - 1))`, whose exact value is `x + √(x² - 1)`, with a relative error below
`1.77 · 2 ^ -53` (`F64RelError`).  Then `log z` lies within `2 ^ -52` of `arcosh x`, both are at
least 1, and `F64Compose.within_two_of_close` gives two steps.
-/

namespace Library.Numerics.Float64.Asinh.AcoshTheoremMid
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RelError Library.Numerics.Float64.Atan.AtanTheoremBranches
  AsinhTheoremBranches AsinhTheoremMid

set_option exponentiation.threshold 4096

theorem arcosh_ge (x : ℝ) (hx : 2 ≤ x) : 9 / 8 ≤ Real.arcosh x := by
  have hs : 17 / 10 ≤ Real.sqrt (x ^ 2 - 1) :=
    (Real.le_sqrt (by norm_num) (by nlinarith)).mpr (by nlinarith)
  have hy : 0 < (x + Real.sqrt (x ^ 2 - 1)) / 2 := by positivity
  have h3 := Real.one_sub_inv_le_log_of_pos hy
  have h4 : Real.arcosh x = Real.log 2 + Real.log ((x + Real.sqrt (x ^ 2 - 1)) / 2) := by
    rw [Real.arcosh, Real.log_div (by positivity) (by norm_num)]
    ring
  have h5 : ((x + Real.sqrt (x ^ 2 - 1)) / 2)⁻¹ ≤ 20 / 37 := by
    rw [inv_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hl := Real.log_two_gt_d9
  norm_num at hl
  linarith

/-- `2 ≤ x ≤ 2 ^ 28`. -/
theorem acosh_mid (x : Float) (hx : Finite x.toBits) (h2 : 2 ≤ value x.toBits)
    (h28 : value x.toBits ≤ 2 ^ 28) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log.log (2.0 * x - 1.0 / (x + (x * x - 1.0).sqrt))).toBits := by
  set a := value x.toBits with ha
  have ha0 : 0 < a := by linarith
  have hA : RApprox x.toBits a 0 := rapprox_self x.toBits hx ha0
  -- `x * x`
  have hxx : RApprox (x * x).toBits (a * a) (1001 / 1000 / 2 ^ 53) := by
    have h58 : a * a ≤ 2 ^ 28 * 2 ^ 28 := mul_le_mul h28 h28 ha0.le (by positivity)
    have hmul := approx_mul (approx_self x.toBits hx) (approx_self x.toBits hx) a a
      (le_of_eq (abs_of_pos ha0)) (le_of_eq (abs_of_pos ha0)) (a * a) (le_of_eq (by ring))
      (by norm_num at h58 ⊢; linarith)
    rw [← F64Bits.toBits_mul] at hmul
    refine ⟨mul_pos ha0 ha0, hmul.mono ?_⟩
    have h4 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 1000 / 2 ^ 53 * (a * a) := by
      have : (4 : ℝ) ≤ a * a := by nlinarith
      have h5 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 1000 / 2 ^ 53 * 4 := by norm_num
      nlinarith
    nlinarith
  -- `x * x - 1`
  have ht2 := (rapprox_sub hxx one_rapprox (by nlinarith) (1335 / 1000 / 2 ^ 53)
    (by nlinarith) (by nlinarith)).mono (ρ' := 2336 / 1000 / 2 ^ 53) (by norm_num)
  rw [← F64Bits.toBits_sub] at ht2
  -- the square root
  have ht3 := (rapprox_sqrt ht2 (by norm_num)).mono (ρ' := 3337 / 1000 / 2 ^ 53) (by norm_num)
  rw [← F64Bits.toBits_sqrt] at ht3
  set r := Real.sqrt (a * a - 1) with hr
  have hrsq : r * r = a * a - 1 := Real.mul_self_sqrt (by nlinarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hra : r ≤ a := by
    rw [hr, Real.sqrt_le_left ha0.le]
    nlinarith
  have hr17 : 17 / 10 ≤ r := by
    rw [hr]
    exact (Real.le_sqrt (by norm_num) (by nlinarith)).mpr (by nlinarith)
  -- `x + √(x² - 1)`
  have ht4 := (rapprox_add hA ht3 (3337 / 1000 / 2 ^ 53) (by nlinarith) (by nlinarith)).mono
    (ρ' := 4338 / 1000 / 2 ^ 53) (by norm_num)
  rw [← F64Bits.toBits_add] at ht4
  -- `1/(x + √(x² - 1))`
  have hq0 : 0 < 1 / (a + r) := by positivity
  have ht5 := (rapprox_div one_rapprox ht4 (by norm_num) (1 / 2 ^ 1040)
    (by
      have h3 : 1 / 2 ^ 30 ≤ 1 / (a + r) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h5 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1040 * (1 / 2 ^ 30) := by norm_num
      have h6 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 1040)
      linarith)
    (by
      have h3 : 1 / (a + r) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have h4 : (1 + 0) / (1 - 4338 / 1000 / 2 ^ 53 : ℝ) ≤ 2 := by norm_num
      nlinarith)).mono (ρ' := 5340 / 1000 / 2 ^ 53) (by norm_num)
  rw [← F64Bits.toBits_div] at ht5
  -- `2 x`
  obtain ⟨h2f, h2v⟩ := Library.Numerics.Float64.Atan.AtanTheoremReduce.double_float x hx
    (by rw [abs_of_pos ha0]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 2)])
    (by rw [abs_of_pos ha0]; linarith [(by norm_num : (2 : ℝ) ^ 28 < 2 ^ 900)])
  have h2a : RApprox (2.0 * x).toBits (2 * a) 0 := by
    have h := rapprox_self _ h2f (by rw [h2v]; linarith)
    rwa [h2v] at h
  -- the argument `z`
  have hq1 : 1 / (a + r) ≤ 1 / a := one_div_le_one_div_of_le ha0 (by linarith)
  have hq2 : 1 / a ≤ a / 4 := by
    rw [div_le_div_iff₀ ha0 (by norm_num)]
    nlinarith
  have hz := (rapprox_sub h2a ht5 (by linarith) (764 / 1000 / 2 ^ 53) (by linarith)
    (by linarith)).mono (ρ' := 1765 / 1000 / 2 ^ 53) (by norm_num)
  rw [← F64Bits.toBits_sub] at hz
  have hzv : 2 * a - 1 / (a + r) = a + Real.sqrt (a ^ 2 - 1) := by
    have hr' : Real.sqrt (a ^ 2 - 1) = r := by rw [hr]; congr 1; ring
    have hne : a + r ≠ 0 := (by linarith : (0 : ℝ) < a + r).ne'
    have hinv : 1 / (a + r) = a - r := by
      rw [div_eq_iff hne]
      nlinarith [hrsq]
    rw [hr', hinv]
    ring
  rw [hzv] at hz
  set w := 2.0 * x - 1.0 / (x + (x * x - 1.0).sqrt) with hw
  have hwpos : 0 < value w.toBits := by
    have := hz.bounds.1
    have : (0 : ℝ) < a + Real.sqrt (a ^ 2 - 1) := by positivity
    nlinarith
  have hlog := Library.Numerics.Float64.Log.LogTheorem.log_within_one w hz.2.1 hwpos
  have hcl := log_close (value w.toBits) (a + Real.sqrt (a ^ 2 - 1)) (1765 / 1000 / 2 ^ 53)
    (by positivity) (by norm_num) hz.2.2
  have hy2 := arcosh_ge a h2
  have hB1 : value (UInt64.ofNat (1023 * 2 ^ 52)) = 1 := by
    rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]
    norm_num
  have hy1 : 1 ≤ Real.log (value w.toBits) := by
    have h3 : (1765 / 1000 / 2 ^ 53 : ℝ) / (1 - 1765 / 1000 / 2 ^ 53) ≤ 1 / 8 := by norm_num
    rw [Real.arcosh] at hy2
    have := (abs_le.mp hcl).1
    linarith
  have hyt : Real.arcosh a ≤ 2 ^ 30 := by
    have h3 : Real.arcosh a ≤ a + Real.sqrt (a ^ 2 - 1) - 1 := by
      rw [Real.arcosh]
      exact Real.log_le_sub_one_of_pos (by positivity)
    have h4 : Real.sqrt (a ^ 2 - 1) ≤ a := by
      rw [Real.sqrt_le_left ha0.le]
      nlinarith
    linarith
  refine F64Compose.within_two_of_close _ _ _ hlog 1023 (by norm_num) (by norm_num)
    (by rw [hB1]; exact hy1) (by rw [hB1]; linarith) ?_ ?_ ?_
  · rw [Real.arcosh]
    have h3 : (1765 / 1000 / 2 ^ 53 : ℝ) / (1 - 1765 / 1000 / 2 ^ 53) <
        (2 : ℝ) ^ (1023 - 1) / 2 ^ 1074 := by
      norm_num
    exact lt_of_le_of_lt hcl h3
  · rw [show F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - 2 ^ 970 from rfl]
    have := (abs_le.mp hcl).2
    have h3 : (1765 / 1000 / 2 ^ 53 : ℝ) / (1 - 1765 / 1000 / 2 ^ 53) ≤ 1 := by norm_num
    rw [Real.arcosh] at hyt
    linarith [(by norm_num : (2 : ℝ) ^ 30 + 1 < 2 ^ 1024 - 2 ^ 970)]
  · rw [show F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - 2 ^ 970 from rfl]
    linarith [(by norm_num : (2 : ℝ) ^ 30 < 2 ^ 1024 - 2 ^ 970)]

#print axioms acosh_mid

end Library.Numerics.Float64.Asinh.AcoshTheoremMid
