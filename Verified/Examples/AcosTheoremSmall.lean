import Verified.Examples.AcosTheoremBranches

/-!
`Asin.acos x` for `|x| < 1/2`.  Below `2 ^ -57` the code returns `pio2_hi + pio2_lo`, and from
there it computes `pio2_hi - (x - (pio2_lo - x r(x²)))`.  The result lies in `[1, 2.1)`, where
the last subtraction rounds to a nearest word of its exact value, so the criterion of
`F64RoundNearest.sub_within` allows a total error of one spacing `2 ^ -52`.
-/

namespace Verified.Examples.AcosTheoremSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest PolyBound AsinTheoremSupport
  AsinTheoremRatio AsinTheoremBranches AsinTheoremSmall AcosTheoremBranches

set_option exponentiation.threshold 4096

theorem hi_finite : Finite (0x3FF921FB54442D18 : UInt64) := by
  unfold CodeLib.IEEE64.Finite; decide +kernel

theorem lo_finite : Finite (0x3C91A62633145C07 : UInt64) := by
  unfold CodeLib.IEEE64.Finite; decide +kernel

theorem lo_bound : |value (0x3C91A62633145C07 : UInt64)| ≤ 1 / 10 ^ 16 :=
  le_trans (abs_value_le _ ((1 / 10 ^ 16 : ℚ)) (by decide +kernel)) (by norm_num)

theorem one_boundary : value (UInt64.ofNat (1023 * 2 ^ 52)) = 1 := by
  rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]
  norm_num

/-- `arccos a ≥ π/3` for `|a| ≤ 1/2`. -/
theorem arccos_ge_third (a : ℝ) (h : |a| ≤ 1 / 2) : Real.pi / 3 ≤ Real.arccos a := by
  have hs : Real.arcsin (1 / 2) = Real.pi / 6 := by
    rw [← Real.sin_pi_div_six, Real.arcsin_sin (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])]
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hm := Real.arcsin_le_arcsin h2
  rw [hs] at hm
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith

/-- `pio2_hi + pio2_lo` for `|x| < 2 ^ -56`. -/
theorem tiny_within (x : Float) (h : |value x.toBits| < 1 / 2 ^ 56) :
    F64SignedRounding.WithinSteps 1 (Real.arccos (value x.toBits)) (pio2HiF + pio2LoF).toBits := by
  have hpi := AtanTheoremConst.atan_inf
  have ha := abs_arcsin_le (value x.toBits) (by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 56 ≤ 1)])
  have hy : Real.arccos (value x.toBits) = Real.pi / 2 - Real.arcsin (value x.toBits) :=
    Real.arccos_eq_pi_div_two_sub_arcsin _
  have hd : |value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 -
      Real.arccos (value x.toBits)| ≤ 1 / 2 ^ 64 + 2 / 2 ^ 56 := by
    rw [hy, show value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 -
      (Real.pi / 2 - Real.arcsin (value x.toBits)) = (value 0x3FF921FB54442D18 +
        value 0x3C91A62633145C07 - Real.pi / 2) + Real.arcsin (value x.toBits) by ring]
    refine (abs_add_le _ _).trans ?_
    have h2 : 2 * |value x.toBits| ≤ 2 / 2 ^ 56 := by linarith
    linarith
  have hp := Real.pi_gt_three
  have hp4 := Real.pi_lt_four
  obtain ⟨hs1, hs2⟩ := abs_le.mp (ha.trans (by linarith : 2 * |value x.toBits| ≤ 2 / 2 ^ 56))
  unfold pio2HiF pio2LoF
  refine add_within (fapprox_ofBits _ hi_finite) (fapprox_ofBits _ lo_finite)
    (Real.arccos (value x.toBits)) (1 / 2 ^ 54) ?_ 1023 (by norm_num) (by norm_num) ?_
    (by norm_num) ?_
  · have h3 : (1 : ℝ) / 2 ^ 64 + 2 / 2 ^ 56 ≤ 1 / 2 ^ 54 := by norm_num
    linarith
  · rw [one_boundary, hy, abs_of_pos (by linarith)]
    have h3 : (1 : ℝ) + 1 / 2 ^ 54 + 2 / 2 ^ 56 ≤ 3 / 2 := by norm_num
    linarith
  · rw [hy, abs_lt]
    have h3 : (4 : ℝ) < 2 ^ 1022 := by norm_num
    constructor <;> linarith

/-- The finish for `|x| < 1/2` from a bound `MR` on `r(x²)` and an absolute error `ER`. -/
theorem small_core (x : Float) (hx : Finite x.toBits) (h1 : |value x.toBits| < 1 / 2)
    (MR ER : ℝ)
    (hrA : FApprox (Asin.asinRatio (x * x))
      (value x.toBits * value x.toBits * eval AsinKernelPoly.asinP (value x.toBits * value x.toBits) /
        eval AsinKernelPoly.asinQ (value x.toBits * value x.toBits)) ER)
    (hrM : |value x.toBits * value x.toBits *
      eval AsinKernelPoly.asinP (value x.toBits * value x.toBits) /
        eval AsinKernelPoly.asinQ (value x.toBits * value x.toBits)| ≤ MR)
    (hMR : MR ≤ 1 / 10) (hER : ER ≤ 1 / 2 ^ 53) :
    F64SignedRounding.WithinSteps 1 (Real.arccos (value x.toBits))
      (pio2HiF - (x - (pio2LoF - x * Asin.asinRatio (x * x)))).toBits := by
  set v := value x.toBits with hv
  set R := v * v * eval AsinKernelPoly.asinP (v * v) / eval AsinKernelPoly.asinQ (v * v) with hR
  have hER0 : 0 ≤ ER := le_trans (abs_nonneg _) hrA.2
  have hrA' := Approx.mono hrA hER
  have hrM' := hrM.trans hMR
  have hxA : FApprox x v 0 := approx_self x.toBits hx
  -- `x r`
  have hxr := fapprox_mul hxA hrA' (1 / 2) (1 / 10) h1.le hrM' ((1 / 2) * (1 / 10 + 1 / 2 ^ 53))
    (le_of_eq (by ring)) (by norm_num)
  have hvr : |v * R| ≤ 1 / 2 * (1 / 10) := by
    rw [abs_mul]
    exact mul_le_mul h1.le hrM' (abs_nonneg _) (by norm_num)
  -- `pio2_lo - x r`
  have hloA := fapprox_ofBits 0x3C91A62633145C07 lo_finite
  set e1 := 0 * (1 / 10) + 1 / 2 * (1 / 2 ^ 53) + 0 * (1 / 2 ^ 53) +
    1 / 2 * (1 / 10 + 1 / 2 ^ 53) / 2 ^ 53 + 1 / 2 ^ 1075 with he1
  have he1b : e1 ≤ 6 / 10 / 2 ^ 53 := by rw [he1]; norm_num
  have h2 := fapprox_sub hloA hxr (52 / 1000) (by
    have h3 := abs_sub (value 0x3C91A62633145C07) (v * R)
    have h4 := lo_bound
    have h5 : (1 : ℝ) / 10 ^ 16 + 1 / 2 * (1 / 10) + (0 + 6 / 10 / 2 ^ 53) ≤ 52 / 1000 := by
      norm_num
    linarith) (by norm_num)
  have hloR : |value 0x3C91A62633145C07 - v * R| ≤ 51 / 1000 := by
    have h3 := abs_sub (value 0x3C91A62633145C07) (v * R)
    have h4 := lo_bound
    have h5 : (1 : ℝ) / 10 ^ 16 + 1 / 2 * (1 / 10) ≤ 51 / 1000 := by norm_num
    linarith
  -- `x - (pio2_lo - x r)`
  have h3 := fapprox_sub hxA h2 (56 / 100) (by
    have h4 := abs_sub v (value 0x3C91A62633145C07 - v * R)
    have h5 : (0 : ℝ) + (0 + e1 + 52 / 1000 / 2 ^ 53) ≤ 1 / 1000 := by
      have : 0 + (6 / 10 / 2 ^ 53 : ℝ) + 52 / 1000 / 2 ^ 53 ≤ 1 / 1000 := by norm_num
      linarith
    linarith) (by norm_num)
  -- the exact value against `arccos x`
  have hpi := AtanTheoremConst.atan_inf
  have hker := asin_kernel v (by linarith)
  rw [← hR] at hker
  have hk3 : |v| ^ 3 * ((11 / 16) / 2 ^ 56) ≤ (1 / 2) ^ 3 * ((11 / 16) / 2 ^ 56) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg v) h1.le 3) (by positivity)
  have hd : |value 0x3FF921FB54442D18 - (v - (value 0x3C91A62633145C07 - v * R)) -
      Real.arccos v| ≤ 1 / 2 ^ 64 + (1 / 2) ^ 3 * ((11 / 16) / 2 ^ 56) := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin, show value 0x3FF921FB54442D18 -
      (v - (value 0x3C91A62633145C07 - v * R)) - (Real.pi / 2 - Real.arcsin v) =
        (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2) +
          (Real.arcsin v - (v + v * R)) by ring]
    refine (abs_add_le _ _).trans ?_
    linarith
  have hp := Real.pi_gt_d2
  have hp4 := Real.pi_lt_four
  have hy3 := arccos_ge_third v h1.le
  have hyp := Real.arccos_le_pi v
  unfold pio2HiF pio2LoF
  refine sub_within (fapprox_ofBits _ hi_finite) h3 (Real.arccos v) ((3 / 2) / 2 ^ 53) ?_ 1023
    (by norm_num) (by norm_num) ?_ (by norm_num) ?_
  · have h4 : (0 : ℝ) + (0 + (0 + e1 + 52 / 1000 / 2 ^ 53) + 56 / 100 / 2 ^ 53) +
        (1 / 2 ^ 64 + (1 / 2) ^ 3 * ((11 / 16) / 2 ^ 56)) ≤ (3 / 2) / 2 ^ 53 := by
      have : (0 : ℝ) + (0 + (0 + 6 / 10 / 2 ^ 53 + 52 / 1000 / 2 ^ 53) + 56 / 100 / 2 ^ 53) +
          (1 / 2 ^ 64 + (1 / 2) ^ 3 * ((11 / 16) / 2 ^ 56)) ≤ (3 / 2) / 2 ^ 53 := by norm_num
      linarith
    linarith
  · rw [one_boundary, abs_of_pos (by linarith)]
    have h4 : (1 : ℝ) + (3 / 2) / 2 ^ 53 ≤ 314 / 100 / 3 := by norm_num
    linarith
  · rw [abs_lt]
    have h4 : (4 : ℝ) < 2 ^ 1022 := by norm_num
    constructor <;> linarith

/-- `|x| < 1/2` from `2 ^ -58` up. -/
theorem small_within (x : Float) (hx : Finite x.toBits) (h0 : 1 / 2 ^ 58 ≤ |value x.toBits|)
    (h1 : |value x.toBits| < 1 / 2) :
    F64SignedRounding.WithinSteps 1 (Real.arccos (value x.toBits))
      (pio2HiF - (x - (pio2LoF - x * Asin.asinRatio (x * x)))).toBits := by
  set v := value x.toBits with hv
  set σ := max |v| (1 / 2 ^ 27) with hσ
  have hσ1 : |v| ≤ σ := le_max_left _ _
  have hσ2 : 1 / 2 ^ 27 ≤ σ := le_max_right _ _
  have hσh : σ < 1 / 2 := max_lt h1 (by norm_num)
  have hσp : 0 < σ := lt_of_lt_of_le (by positivity) hσ2
  have hfx := fsapprox_input x hx σ hσp (by linarith) hσ1
  have hss : 1 / 2 ^ 54 ≤ σ * σ := by
    have := mul_le_mul hσ2 hσ2 (by positivity) hσp.le
    norm_num at this ⊢
    linarith
  have hη : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * σ) := by
    have := mul_le_mul_of_nonneg_left hss (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 960)
    norm_num at this ⊢
    linarith
  have ht := (fsapprox_mul hfx hfx (1 / 2 ^ 960) hη (by norm_num)).mono (M' := 1)
    (e' := (10001 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hvv : v * v ≤ σ * σ := by
    rw [← abs_mul_abs_self v]
    exact mul_le_mul hσ1 hσ1 (abs_nonneg _) hσp.le
  have hσ4 : σ * σ ≤ 1 / 4 := by nlinarith
  rcases le_or_gt (σ * σ) (1 / 8) with hs | hs
  · have hr := ratio_S1 (x * x) _ _ ht (mul_self_nonneg _) (hvv.trans hs) hs hss
    rw [ratio_eval] at hr
    obtain ⟨hrA, hrM⟩ := Log1pTheoremTail.fsapprox_abs hr hs
    exact small_core x hx h1 _ _ hrA hrM (by norm_num) (by norm_num)
  · -- `σ = |x|` here
    have hσv : σ = |v| := by
      rcases le_total |v| (1 / 2 ^ 27) with hle | hle
      · exfalso
        have : σ = 1 / 2 ^ 27 := max_eq_right hle
        rw [this] at hs
        norm_num at hs
      · exact max_eq_left hle
    have hlo : 1 / 8 ≤ v * v := by
      rw [← abs_mul_abs_self v, ← hσv]
      exact hs.le
    have hr := ratio_S2 (x * x) _ _ ht hlo (hvv.trans hσ4) hσ4 hss
    rw [ratio_eval] at hr
    obtain ⟨hrA, hrM⟩ := Log1pTheoremTail.fsapprox_abs hr hσ4
    exact small_core x hx h1 _ _ hrA hrM (by norm_num) (by norm_num)

#print axioms tiny_within
#print axioms small_within

end Verified.Examples.AcosTheoremSmall
