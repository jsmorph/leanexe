import Verified.Examples.SinpiTinySplit
import Verified.Examples.SinpiTinyReal
import LeanExe.ProofKit.F64RelativeStepLow
import Verified.Examples.SinpiSin

/-!
`Sinpi.sinpi` and `Sinpi.tanpi` below `2 ^ -29` in magnitude: within one step of `sin (π x)` and
`tan (π x)` for every finite `x`.  `±0` gives itself.  Otherwise `Sinpi.piTiny` lies within
`(1 + 2 ^ -10) u` of `π x`, relative to the larger of `|π x|` and `2 ^ -1021`, plus `2 ^ -1085`,
and `sin (π x)` and `tan (π x)` lie within `|π x| ^ 3` of `π x`, so that
`F64RelativeStepLow.within_low` applies, subnormal results included.
-/

namespace Verified.Examples.SinpiTiny

open CodeLib.IEEE64 LeanExe.ProofKit TanWords TanTrunc TanBigWords SinpiProduct SinpiTinyWords
  SinpiTinySplit SinpiTinyReal F64RelativeStepLow SinpiCommon SinpiKernels SinpiSin

set_option exponentiation.threshold 1200

/-- The adaptive bound of a rounded product. -/
theorem adaptive_le (n : Nat) (a : ℝ) (ha : 0 ≤ a) :
    (if n = 0 then (0 : ℝ) else max a minNormal64) ≤ a + 1 / 2 ^ 1022 := by
  have hm : minNormal64 = 1 / 2 ^ 1022 := rfl
  have h0 : (0 : ℝ) ≤ 1 / 2 ^ 1022 := by positivity
  split
  · linarith
  · rw [hm]
    exact max_le (by linarith) (by linarith)

/-- The error of `Sinpi.piTiny` on words. -/
theorem tiny_spec (b : UInt64) (hbf : Finite b) (hb1 : |value b| < 1 / 2 ^ 29) :
    Finite (tinyW b) ∧
      |value (tinyW b) - Real.pi * value b| ≤
        (1 + 1 / 2 ^ 10) * (1 / 2 ^ 53) * max |Real.pi * value b| (1 / 2 ^ 1021) +
          1 / 2 ^ 1085 := by
  obtain ⟨fHi, fLo, hC, fC, vHi, vLo, vC, mHi⟩ := const_facts
  have hb1' : |value b| < 1 := lt_trans hb1 (by norm_num)
  obtain ⟨hAf, hHf, hLf, hAv, hLv, hHA, hLA, q, hq, hHm⟩ := split_spec b hbf hb1'
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hk : Wasm.IEEE64.exponent b ≤ 1022 := exp_small b hb1'
  unfold tinyW
  dsimp only
  rw [hC]
  set A := Wasm.IEEE64.mul b P53 with hA
  set H := Wasm.IEEE64.mul (b &&& mask) P53 with hH
  set L := Wasm.IEEE64.sub A H with hL
  -- Magnitudes.
  have hAb : |value A| ≤ 2 ^ 24 := by
    rw [hAv, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53)]
    have : |value b| * 2 ^ 53 ≤ 1 / 2 ^ 29 * 2 ^ 53 :=
      mul_le_mul_of_nonneg_right hb1.le (by positivity)
    have e : (1 : ℝ) / 2 ^ 29 * 2 ^ 53 = 2 ^ 24 := by norm_num
    linarith
  have hLb : |value L| ≤ 2 ^ 5 := by
    have : (2 : ℝ) ^ 24 / 2 ^ 20 + 1 / 2 ^ 989 ≤ 2 ^ 5 := by norm_num
    have h2 : |value A| / 2 ^ 20 ≤ 2 ^ 24 / 2 ^ 20 := div_le_div_of_nonneg_right hAb (by positivity)
    linarith
  have hcpi : |value piC| ≤ 4 := by rw [vC, abs_of_pos (by positivity)]; norm_num
  have hlpi : |value piLo| ≤ 1 := by rw [vLo, abs_neg, abs_of_pos (by positivity)]; norm_num
  have hhpi : |value piHi| ≤ 4 := by rw [vHi, abs_of_pos (by positivity)]; norm_num
  have m1 : |value piC * value L| ≤ 2 ^ 7 := by
    rw [abs_mul]
    calc |value piC| * |value L| ≤ 4 * 2 ^ 5 :=
          mul_le_mul hcpi hLb (abs_nonneg _) (by norm_num)
      _ = 2 ^ 7 := by norm_num
  have m2 : |value piLo * value H| ≤ 2 ^ 24 := by
    rw [abs_mul]
    calc |value piLo| * |value H| ≤ 1 * 2 ^ 24 :=
          mul_le_mul hlpi (le_trans hHA hAb) (abs_nonneg _) (by norm_num)
      _ = 2 ^ 24 := by norm_num
  have m3 : |value piHi * value H| ≤ 2 ^ 26 := by
    rw [abs_mul]
    calc |value piHi| * |value H| ≤ 4 * 2 ^ 24 :=
          mul_le_mul hhpi (le_trans hHA hAb) (abs_nonneg _) (by norm_num)
      _ = 2 ^ 26 := by norm_num
  -- The two rounded products.
  obtain ⟨f1, e1⟩ := F64MulBounds.mul_real_adaptive piC L fC hLf (by
    have : (2 : ℝ) ^ 7 < 2 ^ 1022 := by norm_num
    linarith)
  dsimp only at e1
  have e1' := le_trans e1 (mul_le_mul_of_nonneg_left (adaptive_le _ _ (abs_nonneg _))
    (by rw [hu]; positivity))
  obtain ⟨f2, e2⟩ := F64MulBounds.mul_real_adaptive piLo H fLo hHf (by
    have : (2 : ℝ) ^ 24 < 2 ^ 1022 := by norm_num
    linarith)
  dsimp only at e2
  have e2' := le_trans e2 (mul_le_mul_of_nonneg_left (adaptive_le _ _ (abs_nonneg _))
    (by rw [hu]; positivity))
  set p1 := Wasm.IEEE64.mul piC L with hp1
  set p2 := Wasm.IEEE64.mul piLo H with hp2
  rw [hu] at e1' e2'
  have hp1b : |value p1| ≤ 2 ^ 8 := by
    have := abs_sub_abs_le_abs_sub (value p1) (value piC * value L)
    have : (1 : ℝ) / 2 ^ 53 * (2 ^ 7 + 1 / 2 ^ 1022) ≤ 2 ^ 7 := by norm_num
    linarith
  have hp2b : |value p2| ≤ 2 ^ 25 := by
    have := abs_sub_abs_le_abs_sub (value p2) (value piLo * value H)
    have : (1 : ℝ) / 2 ^ 53 * (2 ^ 24 + 1 / 2 ^ 1022) ≤ 2 ^ 24 := by norm_num
    linarith
  -- The first sum.
  have hsum1 : |value p1 + value p2| ≤ 2 ^ 26 := by
    have := abs_add_le (value p1) (value p2)
    linarith
  obtain ⟨fa, ea⟩ := F64AddBounds.add_real_relative p1 p2 f1 f2 (by
    have : (2 : ℝ) ^ 26 < 2 ^ 1023 := by norm_num
    linarith)
  set a1 := Wasm.IEEE64.add p1 p2 with ha1
  rw [hu] at ea
  have ha1b : |value a1| ≤ 2 ^ 27 := by
    have := abs_sub_abs_le_abs_sub (value a1) (value p1 + value p2)
    have : (1 : ℝ) / 2 ^ 53 * 2 ^ 26 ≤ 2 ^ 26 := by norm_num
    linarith
  -- The exact product and the second sum.
  obtain ⟨fD, vD, -, -⟩ := F64ExactProduct.mul_exact_scaled piHi H fHi hHf 52707179 q 1050
    (Wasm.IEEE64.exponent b - 1 + 85) mHi hHm (by omega) (by omega) (by omega)
  set D := Wasm.IEEE64.mul piHi H with hD
  have hsum2 : |value a1 + value D| ≤ 2 ^ 28 := by
    have := abs_add_le (value a1) (value D)
    rw [vD] at this ⊢
    linarith
  obtain ⟨fs, es⟩ := F64AddBounds.add_real_relative a1 D fa fD (by
    have : (2 : ℝ) ^ 28 < 2 ^ 1023 := by norm_num
    linarith)
  set s := Wasm.IEEE64.add a1 D with hs
  rw [hu] at es
  have hsb : |value s| < 2 ^ 30 := by
    have := abs_sub_abs_le_abs_sub (value s) (value a1 + value D)
    have : (1 : ℝ) / 2 ^ 53 * 2 ^ 28 ≤ 2 ^ 28 := by norm_num
    linarith
  obtain ⟨fr, r1, r2⟩ := mul_down s fs hsb
  refine ⟨fr, ?_⟩
  rw [vC] at e1'
  rw [vLo] at e2'
  have hE := sum_error (value A) (value H) (value L) (value p1) (value p2) (value a1) hLv hLA hHA
    e1' e2' ea
  rw [vD, vHi] at es
  exact final_error (value b) (value A) (value a1 + 52707179 / 2 ^ 24 * value H) (value s)
    (value (Wasm.IEEE64.mul s Pm53)) hAv hE es r1 r2

/-- A nonzero finite word is at least `2 ^ -1074` in magnitude. -/
theorem abs_ge_min (w : UInt64) (h : value w ≠ 0) : 1 / 2 ^ 1074 ≤ |value w| := by
  rw [F64RoundNearest.abs_value]
  have h0 : Wasm.IEEE64.scaledMagnitude w ≠ 0 := by
    intro h0
    apply h
    rw [← abs_eq_zero, F64RoundNearest.abs_value, h0]
    simp
  have : (1 : ℝ) ≤ Wasm.IEEE64.scaledMagnitude w := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  exact div_le_div_of_nonneg_right this (by positivity)

/-- A word within the bound of `tiny_spec` of `T` lies within one step of every `Y` within
`|T| ^ 3` of `T`. -/
theorem close_within (Y T : ℝ) (c : UInt64) (hcf : Finite c) (hT0 : 3 / 2 ^ 1074 ≤ |T|)
    (hT1 : |T| ≤ 315 / 100 / 2 ^ 29)
    (hc : |value c - T| ≤
      (1 + 1 / 2 ^ 10) * (1 / 2 ^ 53) * max |T| (1 / 2 ^ 1021) + 1 / 2 ^ 1085)
    (hY : |Y - T| ≤ |T| ^ 3) :
    F64SignedRounding.WithinSteps 1 Y c := by
  have h3 : |T| ^ 3 ≤ 10 / 2 ^ 58 * |T| := by
    have h2 : |T| ^ 2 ≤ 10 / 2 ^ 58 := by
      calc |T| ^ 2 ≤ (315 / 100 / 2 ^ 29) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hT1 2
        _ ≤ 10 / 2 ^ 58 := by norm_num
    calc |T| ^ 3 = |T| ^ 2 * |T| := by ring
      _ ≤ 10 / 2 ^ 58 * |T| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have t1 := abs_sub_abs_le_abs_sub T Y
  rw [abs_sub_comm T Y] at t1
  have hY0 : 1 / 2 ^ 1073 ≤ |Y| := by
    have : (1 : ℝ) / 2 ^ 1073 ≤ 3 / 2 ^ 1074 * (1 - 10 / 2 ^ 58) := by norm_num
    linarith
  apply within_low Y c hcf hY0
  have tri := abs_sub_le (value c) T Y
  rw [abs_sub_comm T Y] at tri
  have hM1 := le_max_left |Y| (1 / 2 ^ 1021)
  have hM2 := le_max_right |Y| (1 / 2 ^ 1021)
  have hmT : max |T| (1 / 2 ^ 1021) ≤ max |Y| (1 / 2 ^ 1021) + 10 / 2 ^ 58 * |T| := by
    rcases le_total |T| (1 / 2 ^ 1021) with h | h
    · rw [max_eq_right h]
      have : (0 : ℝ) ≤ 10 / 2 ^ 58 * |T| := by positivity
      linarith
    · rw [max_eq_left h]
      linarith
  rw [show unitRoundoff64 = 1 / 2 ^ 53 from rfl]
  linarith

theorem zero_float : Finite (0.0 : Float).toBits ∧ value (0.0 : Float).toBits = 0 := by
  rw [(zero_bits').1]
  exact ⟨by unfold CodeLib.IEEE64.Finite; decide, TanBigWords.value_zero⟩

/-- The bounds on `π x` below `2 ^ -29`. -/
theorem pi_x (X : ℝ) (h0 : 1 / 2 ^ 1074 ≤ |X|) (h1 : |X| < 1 / 2 ^ 29) :
    3 / 2 ^ 1074 ≤ |Real.pi * X| ∧ |Real.pi * X| ≤ 315 / 100 / 2 ^ 29 ∧
      |Real.pi * X| ≤ 1 / 10 := by
  rw [abs_mul, abs_of_pos Real.pi_pos]
  have hpi := Real.pi_gt_three
  have hpi2 : Real.pi < 315 / 100 := by
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith
  have a : 3 * (1 / 2 ^ 1074) ≤ Real.pi * |X| :=
    mul_le_mul hpi.le h0 (by positivity) Real.pi_pos.le
  have b : Real.pi * |X| ≤ 315 / 100 * (1 / 2 ^ 29) :=
    mul_le_mul hpi2.le h1.le (abs_nonneg _) (by norm_num)
  have c : (315 : ℝ) / 100 * (1 / 2 ^ 29) ≤ 1 / 10 := by norm_num
  refine ⟨by linarith, by linarith, by linarith⟩

/-- `sinpi` below `2 ^ -29`. -/
theorem sinpi_tiny (x : Float) (hxf : Finite x.toBits) (h : |value x.toBits| < 1 / 2 ^ 29) :
    F64SignedRounding.WithinSteps 1 (Real.sin (Real.pi * value x.toBits))
      (Sinpi.sinpi x).toBits := by
  obtain ⟨c1, c29, -, -⟩ := abs_thresholds x hxf
  obtain ⟨f0, v0⟩ := zero_float
  unfold Sinpi.sinpi
  dsimp only
  rw [if_pos (c1.mpr (by linarith [show (1 : ℝ) / 2 ^ 29 < 1 by norm_num])), if_pos (c29.mpr h)]
  by_cases h0 : value x.toBits = 0
  · rw [if_pos ((feq_iff x 0.0 hxf f0).mpr (by rw [h0, v0])), h0, mul_zero, Real.sin_zero]
    exact F64SelfStep.zero_step _ ((TrigSinCos.zero_iff _).mpr h0)
  · rw [if_neg (fun h' => h0 (by rw [(feq_iff x 0.0 hxf f0).mp h', v0])), tiny_bits x hxf]
    obtain ⟨hf, hb⟩ := tiny_spec x.toBits hxf h
    obtain ⟨p0, p1, p2⟩ := pi_x _ (abs_ge_min _ h0) h
    exact close_within _ _ _ hf p0 p1 hb (sin_near _ p2)

/-- `tanpi` below `2 ^ -29`. -/
theorem tanpi_tiny (x : Float) (hxf : Finite x.toBits) (h : |value x.toBits| < 1 / 2 ^ 29) :
    F64SignedRounding.WithinSteps 1 (Real.tan (Real.pi * value x.toBits))
      (Sinpi.tanpi x).toBits := by
  obtain ⟨c1, c29, -, -⟩ := abs_thresholds x hxf
  obtain ⟨f0, v0⟩ := zero_float
  unfold Sinpi.tanpi
  dsimp only
  rw [if_pos (c1.mpr (by linarith [show (1 : ℝ) / 2 ^ 29 < 1 by norm_num])), if_pos (c29.mpr h)]
  by_cases h0 : value x.toBits = 0
  · rw [if_pos ((feq_iff x 0.0 hxf f0).mpr (by rw [h0, v0])), h0, mul_zero, Real.tan_zero]
    exact F64SelfStep.zero_step _ ((TrigSinCos.zero_iff _).mpr h0)
  · rw [if_neg (fun h' => h0 (by rw [(feq_iff x 0.0 hxf f0).mp h', v0])), tiny_bits x hxf]
    obtain ⟨hf, hb⟩ := tiny_spec x.toBits hxf h
    obtain ⟨p0, p1, p2⟩ := pi_x _ (abs_ge_min _ h0) h
    exact close_within _ _ _ hf p0 p1 hb (tan_near _ p2)

#print axioms tiny_spec
#print axioms close_within
#print axioms sinpi_tiny
#print axioms tanpi_tiny

end Verified.Examples.SinpiTiny
