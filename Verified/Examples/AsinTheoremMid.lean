import Verified.Examples.AsinTheoremBig

/-!
`Asin.asin x` for `1/2 ≤ |x| < 0.975`: with `t = (1 - |x|)/2`, `s = √t`, `w` the high part of
`s`, and `c = (t - w²)/(s + w)`, the code computes `π/4 - (p - q)` with
`p = 2 s r - (pio2_lo - 2c)` and `q = π/4 - 2w`.  Its exact value is `π/2 - 2 (w + c) - 2 √t r`
up to the constants, and `w + c` lies within `2 ^ -70` of `√t`.  The three ranges of `|x|` use the
chains `A1`, `A2`, and `A3` of `AsinTheoremRatio`.
-/

namespace Verified.Examples.AsinTheoremMid
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest F64HalfUlp PolyBound
  AsinTheoremSupport AsinTheoremRatio AsinTheoremBranches AsinTheoremSmall AsinTheoremHalf
  AsinTheoremBig

set_option exponentiation.threshold 4096

set_option maxHeartbeats 1000000 in
theorem mid_A (x : Float) (hx : Finite x.toBits) (h1 : (1 / 2) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (3 / 5)) (hy : 1 / 2 + (49 / 450359962737049600) ≤ Real.arcsin |value x.toBits|) :
    F64SignedRounding.WithinSteps 1 (Real.arcsin |value x.toBits|) (midTail (tOf x)).toBits := by
  obtain ⟨htf, htv⟩ := t_exact x hx (by linarith) (by linarith)
  set a := |value x.toBits| with ha
  set vt := (1 - a) / 2 with hvt
  have hvlo : (1 / 5) ≤ vt := by rw [hvt]; linarith
  have hvhi : vt ≤ (1 / 4) := by rw [hvt]; linarith
  have hvtp : 0 < vt := lt_of_lt_of_le (by norm_num) hvlo
  have ht : FSApprox (tOf x) vt vt 1 0 :=
    (fsapprox_input (tOf x) htf vt hvtp (by linarith) (by rw [htv, abs_of_pos hvtp])).congr htv
  have hr := ratio_A1 (tOf x) vt vt (ht.mono le_rfl (by norm_num)) (by linarith) hvhi hvhi
    (le_trans (by norm_num) hvlo)
  rw [ratio_eval] at hr
  obtain ⟨hrA, hrM⟩ := Log1pTheoremTail.fsapprox_abs hr hvhi
  set rv := vt * eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt with hrv
  have hrM' : |rv| ≤ (2123 / 40000) := hrM.trans (le_of_eq (by norm_num))
  have hrA' := Approx.mono hrA (e' := (271 / 5629499534213120000)) (le_of_eq (by norm_num))
  -- `s = √t`
  have htA : FApprox (tOf x) vt 0 := ⟨htf, by rw [htv, sub_self, abs_zero]⟩
  have hsqrt0 : 0 < Real.sqrt vt := Real.sqrt_pos.mpr hvtp
  have hsqv : Real.sqrt vt * Real.sqrt vt = vt := Real.mul_self_sqrt hvtp.le
  have hsqhi : Real.sqrt vt ≤ (500001 / 1000000) := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hsqlo : (447213 / 1000000) ≤ Real.sqrt vt := by
    rw [Real.le_sqrt (by norm_num) hvtp.le]
    nlinarith
  have hs := Approx.mono (fapprox_sqrt htA vt vt hvtp le_rfl hvtp le_rfl (Real.sqrt vt)
    (by rw [add_zero])) (e' := (500001 / 1000000) / 2 ^ 53) (by
      rw [zero_div, zero_add]
      exact div_le_div_of_nonneg_right hsqhi (by positivity))
  set s := (tOf x).sqrt with hsd
  set vs := value s.toBits with hvs
  obtain ⟨hes1, hes2⟩ := abs_le.mp hs.2
  have hvs0 : 0 < vs := by
    have : ((500001 / 1000000) : ℝ) / 2 ^ 53 < (447213 / 1000000) := by norm_num
    linarith
  -- `w`, the high part of `s`
  have hse : 506 ≤ Wasm.IEEE64.exponent s.toBits :=
    Log1pTheoremCorr.exponent_ge _ 506 (-517) (by norm_num) (by norm_num) (by
      rw [abs_of_pos hvs0, show (2 : ℝ) ^ (-517 : ℤ) = 1 / 2 ^ 517 by norm_num]
      have : (1 : ℝ) / 2 ^ 517 ≤ (447213 / 1000000) - (500001 / 1000000) / 2 ^ 53 := by norm_num
      linarith)
  obtain ⟨hwf, hwle, hwd, q, hq, hqm⟩ := trunc_facts s.toBits hvs0 hs.1 hse
  have hwb : (wOf s).toBits = s.toBits &&& 0xFFFFFFFF00000000 := by
    unfold wOf
    rw [F64Bits.toBits_ofBits, not_nan_of_finite hwf]
    simp only [Bool.false_eq_true, ite_false]
  rw [← hwb] at hwf hwle hwd hqm
  set w := wOf s with hwdef
  set vw := value w.toBits with hvw
  have hvwlo : (447212573 / 1000000000) ≤ vw := by
    have : (447212573 / 1000000000) ≤ vs * (1 - 1 / 2 ^ 20) := by
      have h3 : ((447213 / 1000000) - (500001 / 1000000) / 2 ^ 53) * (1 - 1 / 2 ^ 20) ≤ vs * (1 - 1 / 2 ^ 20) :=
        mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
      have h4 : ((447212573 / 1000000000) : ℝ) ≤ ((447213 / 1000000) - (500001 / 1000000) / 2 ^ 53) * (1 - 1 / 2 ^ 20) := by norm_num
      linarith
    linarith
  have hvw0 : 0 < vw := lt_of_lt_of_le (by norm_num) hvwlo
  have hvwhi : vw ≤ (500001 / 1000000) + (500001 / 1000000) / 2 ^ 53 := by linarith
  -- `w * w` and `t - w * w` are exact
  have hww := F64ExactProduct.mul_exact_scaled w.toBits w.toBits hwf hwf q q
    (Wasm.IEEE64.exponent s.toBits - 1 + 32) (Wasm.IEEE64.exponent s.toBits - 1 + 32) hqm hqm
    (lt_of_le_of_lt (Nat.mul_le_mul hq.le hq.le) (by norm_num)) (by omega) (by
      have := AsinTheoremSupport.exponent_lt_one s.toBits (by
        rw [abs_of_pos hvs0]
        have : ((500001 / 1000000) : ℝ) + (500001 / 1000000) / 2 ^ 53 < 1 := by norm_num
        linarith)
      omega)
  rw [← F64Bits.toBits_mul] at hww
  have hwwv : value (w * w).toBits = vw * vw := hww.2.1
  have hwwf := hww.1
  clear hww hqm
  -- `|t - w²|` is small
  have hdw : |Real.sqrt vt - vw| ≤ (500001 / 1000000) / 2 ^ 53 + (500001 / 1000000) / 2 ^ 20 := by
    rw [abs_le]
    constructor
    · linarith
    · have : vs / 2 ^ 20 ≤ ((500001 / 1000000) + (500001 / 1000000) / 2 ^ 53) / 2 ^ 20 :=
        div_le_div_of_nonneg_right (by linarith) (by norm_num)
      have h5 : ((500001 / 1000000) + (500001 / 1000000) / 2 ^ 53 : ℝ) / 2 ^ 20 ≤ (500001 / 1000000) / 2 ^ 20 + (500001 / 1000000) / 2 ^ 53 := by
        norm_num
      linarith
  have htw0 : |vt - vw * vw| ≤ (238419533 / 500000000000000) := by
    rw [show vt - vw * vw = (Real.sqrt vt - vw) * (Real.sqrt vt + vw) by
      linear_combination (-1 : ℝ) * hsqv,
      abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt vt + vw)]
    have h3 : Real.sqrt vt + vw ≤ 2 * (500001 / 1000000) + (500001 / 1000000) / 2 ^ 53 := by linarith
    have h4 := mul_le_mul hdw h3 (by positivity) (by positivity)
    have h5 : ((500001 / 1000000) / 2 ^ 53 + (500001 / 1000000) / 2 ^ 20 : ℝ) * (2 * (500001 / 1000000) + (500001 / 1000000) / 2 ^ 53) ≤
        (238419533 / 500000000000000) := by norm_num
    linarith
  have hwwt1 : vw * vw ≤ 2 * vt := by
    have := (abs_le.mp htw0).1
    have : ((238419533 / 500000000000000) : ℝ) ≤ (1 / 5) := by norm_num
    linarith
  have hwwt2 : vt ≤ 2 * (vw * vw) := by
    have := (abs_le.mp htw0).2
    have : ((238419533 / 500000000000000) : ℝ) ≤ (1 / 5) := by norm_num
    linarith
  have htw := F64Exact.sub_exact (tOf x).toBits (w * w).toBits htf hwwf (by rw [htv]; exact hvtp)
    (by rw [hwwv]; positivity) (by rw [hwwv, htv]; exact hwwt1) (by rw [hwwv, htv]; exact hwwt2)
    (by rw [htv]; linarith [(by norm_num : ((1 / 4) : ℝ) < 2 ^ 900)])
    (by rw [hwwv]; nlinarith [(by norm_num : (4 : ℝ) < 2 ^ 900)])
  rw [← F64Bits.toBits_sub, htv, hwwv] at htw
  have htwA : FApprox (tOf x - w * w) (vt - vw * vw) 0 := ⟨htw.1, by rw [htw.2, sub_self, abs_zero]⟩
  -- `s + w` and `c`
  have hsw := fapprox_add (approx_self s.toBits hs.1) (approx_self w.toBits hwf)
    (2 * ((500001 / 1000000) + (500001 / 1000000) / 2 ^ 53)) (by
      rw [abs_of_pos (by linarith)]
      linarith) (by norm_num)
  have hsw0 : (35777 / 40000) ≤ |vs + vw| := by
    rw [abs_of_pos (by linarith)]
    have : ((35777 / 40000) : ℝ) ≤ ((447213 / 1000000) - (500001 / 1000000) / 2 ^ 53) + (447212573 / 1000000000) := by norm_num
    linarith
  have hc := fapprox_div htwA hsw (238419533 / 500000000000000) (35777 / 40000) htw0 hsw0 (by norm_num) (533123589 / 1000000000000000) (by norm_num)
    (by norm_num)
  set cv := (vt - vw * vw) / (vs + vw) with hcv
  have hcM : |cv| ≤ (533123589 / 1000000000000000) := by
    rw [hcv, abs_div]
    calc |vt - vw * vw| / |vs + vw| ≤ (238419533 / 500000000000000) / |vs + vw| :=
          div_le_div_of_nonneg_right htw0 (abs_nonneg _)
      _ ≤ (238419533 / 500000000000000) / (35777 / 40000) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsw0
      _ ≤ (533123589 / 1000000000000000) := by norm_num
  have h2f : FApprox (2.0 : Float) 2 0 := by
    have := Log1pTheoremCore.two_approx.approx
    rw [zero_mul] at this
    exact this
  have hc2 := fapprox_mul h2f hc 2 (533123589 / 1000000000000000) (by norm_num) hcM (1066247179 / 1000000000000000) (by norm_num) (by norm_num)
  have hlof : Finite (0x3C91A62633145C07 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hh4f : Finite (0x3FE921FB54442D18 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hlov : |value (0x3C91A62633145C07 : UInt64)| ≤ 1 / 10 ^ 16 :=
    le_trans (abs_value_le _ ((1 / 10 ^ 16 : ℚ)) (by decide +kernel)) (by norm_num)
  have h4v : |value (0x3FE921FB54442D18 : UInt64) - 7853981633974483 / 10 ^ 16| ≤ 1 / 10 ^ 16 := by
    rw [← ratOfWord_cast, show ratOfWord 0x3FE921FB54442D18 = 884279719003555 / 2 ^ 50 by
      decide +kernel]
    norm_num [abs_le]
  have hlo2c := fapprox_sub (const_word _ hlof) hc2 (1066247179 / 1000000000000000) (by
    have h3 := abs_sub (value (0x3C91A62633145C07 : UInt64)) (2 * cv)
    rw [abs_mul, abs_two] at h3
    norm_num at h3 hcM hlov ⊢
    linarith) (by norm_num)
  -- `2 s r`
  obtain ⟨h2sf, h2sv⟩ := AtanTheoremReduce.double_float s hs.1 (by
      rw [abs_of_pos hvs0]
      have : (1 : ℝ) / 2 ^ 1000 ≤ (447213 / 1000000) - (500001 / 1000000) / 2 ^ 53 := by norm_num
      linarith) (by
      rw [abs_of_pos hvs0]
      have : ((500001 / 1000000) : ℝ) + (500001 / 1000000) / 2 ^ 53 < 2 ^ 900 := by norm_num
      linarith)
  have hs2 : FApprox (2.0 * s) (2 * Real.sqrt vt) (2 * ((500001 / 1000000) / 2 ^ 53)) := by
    refine ⟨h2sf, ?_⟩
    rw [h2sv, show 2 * vs - 2 * Real.sqrt vt = 2 * (vs - Real.sqrt vt) by ring, abs_mul, abs_two]
    have := hs.2
    linarith
  have hsr := fapprox_mul hs2 hrA' (2 * (500001 / 1000000)) (2123 / 40000) (by
      rw [abs_mul, abs_two, abs_of_pos hsqrt0]; linarith) hrM' (53075107 / 1000000000) (by norm_num)
    (by norm_num)
  have hp := fapprox_sub_half hsr hlo2c 1017 (by norm_num) (by
    have h3 := abs_sub (2 * Real.sqrt vt * rv) (value (0x3C91A62633145C07 : UInt64) - 2 * cv)
    have h4 : |2 * Real.sqrt vt * rv| ≤ 2 * (500001 / 1000000) * (2123 / 40000) := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hsqrt0]
      exact mul_le_mul (by linarith) hrM' (abs_nonneg _) (by norm_num)
    have h5 := abs_sub (value (0x3C91A62633145C07 : UInt64)) (2 * cv)
    rw [abs_mul, abs_two] at h5
    norm_num at h3 h4 h5 hcM hlov ⊢
    linarith)
  -- `q = π/4 - 2 w`
  obtain ⟨h2wf, h2wv⟩ := AtanTheoremReduce.double_float w hwf (by
      rw [abs_of_pos hvw0]
      have : (1 : ℝ) / 2 ^ 1000 ≤ (447212573 / 1000000000) := by norm_num
      linarith) (by
      rw [abs_of_pos hvw0]
      have : ((500001 / 1000000) : ℝ) + (500001 / 1000000) / 2 ^ 53 < 2 ^ 900 := by norm_num
      linarith)
  have hw2 : FApprox (2.0 * w) (2 * vw) 0 := ⟨h2wf, by rw [h2wv, sub_self, abs_zero]⟩
  have hqb : |value (0x3FE921FB54442D18 : UInt64) - 2 * vw| ≤ (214603837 / 1000000000) := by
    rw [abs_le]
    obtain ⟨h5, h6⟩ := abs_le.mp h4v
    constructor <;> norm_num at h5 h6 hvwlo hvwhi ⊢ <;> linarith
  have hq := fapprox_sub_half (const_word _ hh4f) hw2 1019 (by norm_num) (by
    norm_num at hqb ⊢
    linarith)
  have hpq := fapprox_sub_half hp hq 1020 (by norm_num) (by
    have h3 := abs_sub (2 * Real.sqrt vt * rv - (value (0x3C91A62633145C07 : UInt64) - 2 * cv))
      (value (0x3FE921FB54442D18 : UInt64) - 2 * vw)
    have h4 : |2 * Real.sqrt vt * rv| ≤ 2 * (500001 / 1000000) * (2123 / 40000) := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hsqrt0]
      exact mul_le_mul (by linarith) hrM' (abs_nonneg _) (by norm_num)
    have h5 := abs_sub (value (0x3C91A62633145C07 : UInt64)) (2 * cv)
    rw [abs_mul, abs_two] at h5
    have h6 := abs_sub (2 * Real.sqrt vt * rv) (value (0x3C91A62633145C07 : UInt64) - 2 * cv)
    norm_num at h3 h4 h5 h6 hcM hlov hqb ⊢
    linarith)
  -- the exact value against `arcsin a`
  have hy0 := arcsin_half a (by linarith) (by linarith)
  rw [← hvt] at hy0
  have hker := asin_kernel (Real.sqrt vt) (by
    rw [abs_of_pos hsqrt0, Real.sqrt_le_left (by norm_num)]
    linarith)
  rw [hsqv, abs_of_pos hsqrt0] at hker
  have hpi := AtanTheoremConst.atan_inf
  have hh4 : value (0x3FE921FB54442D18 : UInt64) + value (0x3FE921FB54442D18 : UInt64) =
      value (0x3FF921FB54442D18 : UInt64) := by
    rw [← ratOfWord_cast, ← ratOfWord_cast]
    exact_mod_cast (by decide +kernel : ratOfWord 0x3FE921FB54442D18 +
      ratOfWord 0x3FE921FB54442D18 = ratOfWord 0x3FF921FB54442D18)
  have hk3 : Real.sqrt vt ^ 3 ≤ (500001 / 1000000) ^ 3 := pow_le_pow_left₀ hsqrt0.le hsqhi 3
  have hsm : |Real.sqrt vt - vw - cv| ≤ (16543793 / 500000000000000000000000000000) := by
    have hden1 : 0 < Real.sqrt vt + vw := by linarith
    have hden2 : 0 < vs + vw := by linarith
    have hid : Real.sqrt vt - vw - cv = (vt - vw * vw) * (vs - Real.sqrt vt) /
        ((Real.sqrt vt + vw) * (vs + vw)) := by
      rw [hcv]
      set u := Real.sqrt vt with hu
      rw [← hsqv]
      have h5 := hden1.ne'
      have h6 := hden2.ne'
      field_simp
      ring
    rw [hid, abs_div, abs_mul, abs_of_pos (mul_pos hden1 hden2)]
    have h3 : |vs - Real.sqrt vt| ≤ (500001 / 1000000) / 2 ^ 53 := hs.2
    have h4 : ((35777 / 40000) : ℝ) * (35777 / 40000) ≤ (Real.sqrt vt + vw) * (vs + vw) := by
      apply mul_le_mul _ _ (by norm_num) (by linarith)
      · have : ((35777 / 40000) : ℝ) ≤ (447213 / 1000000) + (447212573 / 1000000000) := by norm_num
        linarith
      · have : ((35777 / 40000) : ℝ) ≤ ((447213 / 1000000) - (500001 / 1000000) / 2 ^ 53) + (447212573 / 1000000000) := by norm_num
        linarith
    rw [div_le_iff₀ (mul_pos hden1 hden2)]
    have h5 := mul_le_mul htw0 h3 (abs_nonneg _) (by norm_num)
    have h6 : ((238419533 / 500000000000000) : ℝ) * ((500001 / 1000000) / 2 ^ 53) ≤ (16543793 / 500000000000000000000000000000) * ((35777 / 40000) * (35777 / 40000)) := by
      norm_num
    nlinarith
  have hd : |value (0x3FE921FB54442D18 : UInt64) - ((2 * Real.sqrt vt * rv -
      (value (0x3C91A62633145C07 : UInt64) - 2 * cv)) -
        (value (0x3FE921FB54442D18 : UInt64) - 2 * vw)) - Real.arcsin a| ≤
      1 / 2 ^ 64 + 2 * ((500001 / 1000000) ^ 3 * ((11 / 16) / 2 ^ 56)) + 2 * (16543793 / 500000000000000000000000000000) := by
    rw [hy0, show value (0x3FE921FB54442D18 : UInt64) - ((2 * Real.sqrt vt * rv -
      (value (0x3C91A62633145C07 : UInt64) - 2 * cv)) -
        (value (0x3FE921FB54442D18 : UInt64) - 2 * vw)) -
          (Real.pi / 2 - 2 * Real.arcsin (Real.sqrt vt)) =
        (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2) +
          2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
            eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt))) +
          2 * (Real.sqrt vt - vw - cv) by rw [← hh4, hrv]; ring]
    have h3 := abs_add_le ((value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2) +
      2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
        eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt)))) (2 * (Real.sqrt vt - vw - cv))
    have h4 := abs_add_le (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2)
      (2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
        eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt))))
    rw [abs_mul, abs_two] at h3 h4
    have h5 : Real.sqrt vt ^ 3 * ((11 / 16) / 2 ^ 56) ≤ (500001 / 1000000) ^ 3 * ((11 / 16) / 2 ^ 56) :=
      mul_le_mul_of_nonneg_right hk3 (by positivity)
    linarith
  have hB : value (UInt64.ofNat (1022 * 2 ^ 52)) = 1 / 2 := by
    rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
    norm_num
  have hyt := abs_arcsin_lt a
  refine sub_within (const_word _ hh4f) hpq (Real.arcsin a) (49 / 450359962737049600) ?_ 1022 (by norm_num)
    (by norm_num) ?_ (by norm_num) (lt_trans hyt (by norm_num))
  · norm_num at hd ⊢
    linarith
  · rw [hB, abs_of_pos (by linarith)]
    linarith

set_option maxHeartbeats 1000000 in
theorem mid_B (x : Float) (hx : Finite x.toBits) (h1 : (3 / 5) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (9 / 10)) (hy : 1 / 2 + (49 / 450359962737049600) ≤ Real.arcsin |value x.toBits|) :
    F64SignedRounding.WithinSteps 1 (Real.arcsin |value x.toBits|) (midTail (tOf x)).toBits := by
  obtain ⟨htf, htv⟩ := t_exact x hx (by linarith) (by linarith)
  set a := |value x.toBits| with ha
  set vt := (1 - a) / 2 with hvt
  have hvlo : (1 / 20) ≤ vt := by rw [hvt]; linarith
  have hvhi : vt ≤ (1 / 5) := by rw [hvt]; linarith
  have hvtp : 0 < vt := lt_of_lt_of_le (by norm_num) hvlo
  have ht : FSApprox (tOf x) vt vt 1 0 :=
    (fsapprox_input (tOf x) htf vt hvtp (by linarith) (by rw [htv, abs_of_pos hvtp])).congr htv
  have hr := ratio_A2 (tOf x) vt vt (ht.mono le_rfl (by norm_num)) (by linarith) hvhi hvhi
    (le_trans (by norm_num) hvlo)
  rw [ratio_eval] at hr
  obtain ⟨hrA, hrM⟩ := Log1pTheoremTail.fsapprox_abs hr hvhi
  set rv := vt * eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt with hrv
  have hrM' : |rv| ≤ (2541 / 50000) := hrM.trans (le_of_eq (by norm_num))
  have hrA' := Approx.mono hrA (e' := (18477 / 450359962737049600000)) (le_of_eq (by norm_num))
  -- `s = √t`
  have htA : FApprox (tOf x) vt 0 := ⟨htf, by rw [htv, sub_self, abs_zero]⟩
  have hsqrt0 : 0 < Real.sqrt vt := Real.sqrt_pos.mpr hvtp
  have hsqv : Real.sqrt vt * Real.sqrt vt = vt := Real.mul_self_sqrt hvtp.le
  have hsqhi : Real.sqrt vt ≤ (223607 / 500000) := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hsqlo : (111803 / 500000) ≤ Real.sqrt vt := by
    rw [Real.le_sqrt (by norm_num) hvtp.le]
    nlinarith
  have hs := Approx.mono (fapprox_sqrt htA vt vt hvtp le_rfl hvtp le_rfl (Real.sqrt vt)
    (by rw [add_zero])) (e' := (223607 / 500000) / 2 ^ 53) (by
      rw [zero_div, zero_add]
      exact div_le_div_of_nonneg_right hsqhi (by positivity))
  set s := (tOf x).sqrt with hsd
  set vs := value s.toBits with hvs
  obtain ⟨hes1, hes2⟩ := abs_le.mp hs.2
  have hvs0 : 0 < vs := by
    have : ((223607 / 500000) : ℝ) / 2 ^ 53 < (111803 / 500000) := by norm_num
    linarith
  -- `w`, the high part of `s`
  have hse : 506 ≤ Wasm.IEEE64.exponent s.toBits :=
    Log1pTheoremCorr.exponent_ge _ 506 (-517) (by norm_num) (by norm_num) (by
      rw [abs_of_pos hvs0, show (2 : ℝ) ^ (-517 : ℤ) = 1 / 2 ^ 517 by norm_num]
      have : (1 : ℝ) / 2 ^ 517 ≤ (111803 / 500000) - (223607 / 500000) / 2 ^ 53 := by norm_num
      linarith)
  obtain ⟨hwf, hwle, hwd, q, hq, hqm⟩ := trunc_facts s.toBits hvs0 hs.1 hse
  have hwb : (wOf s).toBits = s.toBits &&& 0xFFFFFFFF00000000 := by
    unfold wOf
    rw [F64Bits.toBits_ofBits, not_nan_of_finite hwf]
    simp only [Bool.false_eq_true, ite_false]
  rw [← hwb] at hwf hwle hwd hqm
  set w := wOf s with hwdef
  set vw := value w.toBits with hvw
  have hvwlo : (111802893 / 500000000) ≤ vw := by
    have : (111802893 / 500000000) ≤ vs * (1 - 1 / 2 ^ 20) := by
      have h3 : ((111803 / 500000) - (223607 / 500000) / 2 ^ 53) * (1 - 1 / 2 ^ 20) ≤ vs * (1 - 1 / 2 ^ 20) :=
        mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
      have h4 : ((111802893 / 500000000) : ℝ) ≤ ((111803 / 500000) - (223607 / 500000) / 2 ^ 53) * (1 - 1 / 2 ^ 20) := by norm_num
      linarith
    linarith
  have hvw0 : 0 < vw := lt_of_lt_of_le (by norm_num) hvwlo
  have hvwhi : vw ≤ (223607 / 500000) + (223607 / 500000) / 2 ^ 53 := by linarith
  -- `w * w` and `t - w * w` are exact
  have hww := F64ExactProduct.mul_exact_scaled w.toBits w.toBits hwf hwf q q
    (Wasm.IEEE64.exponent s.toBits - 1 + 32) (Wasm.IEEE64.exponent s.toBits - 1 + 32) hqm hqm
    (lt_of_le_of_lt (Nat.mul_le_mul hq.le hq.le) (by norm_num)) (by omega) (by
      have := AsinTheoremSupport.exponent_lt_one s.toBits (by
        rw [abs_of_pos hvs0]
        have : ((223607 / 500000) : ℝ) + (223607 / 500000) / 2 ^ 53 < 1 := by norm_num
        linarith)
      omega)
  rw [← F64Bits.toBits_mul] at hww
  have hwwv : value (w * w).toBits = vw * vw := hww.2.1
  have hwwf := hww.1
  clear hww hqm
  -- `|t - w²|` is small
  have hdw : |Real.sqrt vt - vw| ≤ (223607 / 500000) / 2 ^ 53 + (223607 / 500000) / 2 ^ 20 := by
    rw [abs_le]
    constructor
    · linarith
    · have : vs / 2 ^ 20 ≤ ((223607 / 500000) + (223607 / 500000) / 2 ^ 53) / 2 ^ 20 :=
        div_le_div_of_nonneg_right (by linarith) (by norm_num)
      have h5 : ((223607 / 500000) + (223607 / 500000) / 2 ^ 53 : ℝ) / 2 ^ 20 ≤ (223607 / 500000) / 2 ^ 20 + (223607 / 500000) / 2 ^ 53 := by
        norm_num
      linarith
  have htw0 : |vt - vw * vw| ≤ (381470417 / 1000000000000000) := by
    rw [show vt - vw * vw = (Real.sqrt vt - vw) * (Real.sqrt vt + vw) by
      linear_combination (-1 : ℝ) * hsqv,
      abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt vt + vw)]
    have h3 : Real.sqrt vt + vw ≤ 2 * (223607 / 500000) + (223607 / 500000) / 2 ^ 53 := by linarith
    have h4 := mul_le_mul hdw h3 (by positivity) (by positivity)
    have h5 : ((223607 / 500000) / 2 ^ 53 + (223607 / 500000) / 2 ^ 20 : ℝ) * (2 * (223607 / 500000) + (223607 / 500000) / 2 ^ 53) ≤
        (381470417 / 1000000000000000) := by norm_num
    linarith
  have hwwt1 : vw * vw ≤ 2 * vt := by
    have := (abs_le.mp htw0).1
    have : ((381470417 / 1000000000000000) : ℝ) ≤ (1 / 20) := by norm_num
    linarith
  have hwwt2 : vt ≤ 2 * (vw * vw) := by
    have := (abs_le.mp htw0).2
    have : ((381470417 / 1000000000000000) : ℝ) ≤ (1 / 20) := by norm_num
    linarith
  have htw := F64Exact.sub_exact (tOf x).toBits (w * w).toBits htf hwwf (by rw [htv]; exact hvtp)
    (by rw [hwwv]; positivity) (by rw [hwwv, htv]; exact hwwt1) (by rw [hwwv, htv]; exact hwwt2)
    (by rw [htv]; linarith [(by norm_num : ((1 / 5) : ℝ) < 2 ^ 900)])
    (by rw [hwwv]; nlinarith [(by norm_num : (4 : ℝ) < 2 ^ 900)])
  rw [← F64Bits.toBits_sub, htv, hwwv] at htw
  have htwA : FApprox (tOf x - w * w) (vt - vw * vw) 0 := ⟨htw.1, by rw [htw.2, sub_self, abs_zero]⟩
  -- `s + w` and `c`
  have hsw := fapprox_add (approx_self s.toBits hs.1) (approx_self w.toBits hwf)
    (2 * ((223607 / 500000) + (223607 / 500000) / 2 ^ 53)) (by
      rw [abs_of_pos (by linarith)]
      linarith) (by norm_num)
  have hsw0 : (447211 / 1000000) ≤ |vs + vw| := by
    rw [abs_of_pos (by linarith)]
    have : ((447211 / 1000000) : ℝ) ≤ ((111803 / 500000) - (223607 / 500000) / 2 ^ 53) + (111802893 / 500000000) := by norm_num
    linarith
  have hc := fapprox_div htwA hsw (381470417 / 1000000000000000) (447211 / 1000000) htw0 hsw0 (by norm_num) (170599747 / 200000000000000) (by norm_num)
    (by norm_num)
  set cv := (vt - vw * vw) / (vs + vw) with hcv
  have hcM : |cv| ≤ (170599747 / 200000000000000) := by
    rw [hcv, abs_div]
    calc |vt - vw * vw| / |vs + vw| ≤ (381470417 / 1000000000000000) / |vs + vw| :=
          div_le_div_of_nonneg_right htw0 (abs_nonneg _)
      _ ≤ (381470417 / 1000000000000000) / (447211 / 1000000) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsw0
      _ ≤ (170599747 / 200000000000000) := by norm_num
  have h2f : FApprox (2.0 : Float) 2 0 := by
    have := Log1pTheoremCore.two_approx.approx
    rw [zero_mul] at this
    exact this
  have hc2 := fapprox_mul h2f hc 2 (170599747 / 200000000000000) (by norm_num) hcM (1705997471 / 1000000000000000) (by norm_num) (by norm_num)
  have hlof : Finite (0x3C91A62633145C07 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hh4f : Finite (0x3FE921FB54442D18 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hlov : |value (0x3C91A62633145C07 : UInt64)| ≤ 1 / 10 ^ 16 :=
    le_trans (abs_value_le _ ((1 / 10 ^ 16 : ℚ)) (by decide +kernel)) (by norm_num)
  have h4v : |value (0x3FE921FB54442D18 : UInt64) - 7853981633974483 / 10 ^ 16| ≤ 1 / 10 ^ 16 := by
    rw [← ratOfWord_cast, show ratOfWord 0x3FE921FB54442D18 = 884279719003555 / 2 ^ 50 by
      decide +kernel]
    norm_num [abs_le]
  have hlo2c := fapprox_sub (const_word _ hlof) hc2 (1705997471 / 1000000000000000) (by
    have h3 := abs_sub (value (0x3C91A62633145C07 : UInt64)) (2 * cv)
    rw [abs_mul, abs_two] at h3
    norm_num at h3 hcM hlov ⊢
    linarith) (by norm_num)
  -- `2 s r`
  obtain ⟨h2sf, h2sv⟩ := AtanTheoremReduce.double_float s hs.1 (by
      rw [abs_of_pos hvs0]
      have : (1 : ℝ) / 2 ^ 1000 ≤ (111803 / 500000) - (223607 / 500000) / 2 ^ 53 := by norm_num
      linarith) (by
      rw [abs_of_pos hvs0]
      have : ((223607 / 500000) : ℝ) + (223607 / 500000) / 2 ^ 53 < 2 ^ 900 := by norm_num
      linarith)
  have hs2 : FApprox (2.0 * s) (2 * Real.sqrt vt) (2 * ((223607 / 500000) / 2 ^ 53)) := by
    refine ⟨h2sf, ?_⟩
    rw [h2sv, show 2 * vs - 2 * Real.sqrt vt = 2 * (vs - Real.sqrt vt) by ring, abs_mul, abs_two]
    have := hs.2
    linarith
  have hsr := fapprox_mul hs2 hrA' (2 * (223607 / 500000)) (2541 / 50000) (by
      rw [abs_mul, abs_two, abs_of_pos hsqrt0]; linarith) hrM' (45454831 / 1000000000) (by norm_num)
    (by norm_num)
  have hp := fapprox_sub_half hsr hlo2c 1017 (by norm_num) (by
    have h3 := abs_sub (2 * Real.sqrt vt * rv) (value (0x3C91A62633145C07 : UInt64) - 2 * cv)
    have h4 : |2 * Real.sqrt vt * rv| ≤ 2 * (223607 / 500000) * (2541 / 50000) := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hsqrt0]
      exact mul_le_mul (by linarith) hrM' (abs_nonneg _) (by norm_num)
    have h5 := abs_sub (value (0x3C91A62633145C07 : UInt64)) (2 * cv)
    rw [abs_mul, abs_two] at h5
    norm_num at h3 h4 h5 hcM hlov ⊢
    linarith)
  -- `q = π/4 - 2 w`
  obtain ⟨h2wf, h2wv⟩ := AtanTheoremReduce.double_float w hwf (by
      rw [abs_of_pos hvw0]
      have : (1 : ℝ) / 2 ^ 1000 ≤ (111802893 / 500000000) := by norm_num
      linarith) (by
      rw [abs_of_pos hvw0]
      have : ((223607 / 500000) : ℝ) + (223607 / 500000) / 2 ^ 53 < 2 ^ 900 := by norm_num
      linarith)
  have hw2 : FApprox (2.0 * w) (2 * vw) 0 := ⟨h2wf, by rw [h2wv, sub_self, abs_zero]⟩
  have hqb : |value (0x3FE921FB54442D18 : UInt64) - 2 * vw| ≤ (10568331 / 31250000) := by
    rw [abs_le]
    obtain ⟨h5, h6⟩ := abs_le.mp h4v
    constructor <;> norm_num at h5 h6 hvwlo hvwhi ⊢ <;> linarith
  have hq := fapprox_sub_half (const_word _ hh4f) hw2 1020 (by norm_num) (by
    norm_num at hqb ⊢
    linarith)
  have hpq := fapprox_sub_half hp hq 1020 (by norm_num) (by
    have h3 := abs_sub (2 * Real.sqrt vt * rv - (value (0x3C91A62633145C07 : UInt64) - 2 * cv))
      (value (0x3FE921FB54442D18 : UInt64) - 2 * vw)
    have h4 : |2 * Real.sqrt vt * rv| ≤ 2 * (223607 / 500000) * (2541 / 50000) := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hsqrt0]
      exact mul_le_mul (by linarith) hrM' (abs_nonneg _) (by norm_num)
    have h5 := abs_sub (value (0x3C91A62633145C07 : UInt64)) (2 * cv)
    rw [abs_mul, abs_two] at h5
    have h6 := abs_sub (2 * Real.sqrt vt * rv) (value (0x3C91A62633145C07 : UInt64) - 2 * cv)
    norm_num at h3 h4 h5 h6 hcM hlov hqb ⊢
    linarith)
  -- the exact value against `arcsin a`
  have hy0 := arcsin_half a (by linarith) (by linarith)
  rw [← hvt] at hy0
  have hker := asin_kernel (Real.sqrt vt) (by
    rw [abs_of_pos hsqrt0, Real.sqrt_le_left (by norm_num)]
    linarith)
  rw [hsqv, abs_of_pos hsqrt0] at hker
  have hpi := AtanTheoremConst.atan_inf
  have hh4 : value (0x3FE921FB54442D18 : UInt64) + value (0x3FE921FB54442D18 : UInt64) =
      value (0x3FF921FB54442D18 : UInt64) := by
    rw [← ratOfWord_cast, ← ratOfWord_cast]
    exact_mod_cast (by decide +kernel : ratOfWord 0x3FE921FB54442D18 +
      ratOfWord 0x3FE921FB54442D18 = ratOfWord 0x3FF921FB54442D18)
  have hk3 : Real.sqrt vt ^ 3 ≤ (223607 / 500000) ^ 3 := pow_le_pow_left₀ hsqrt0.le hsqhi 3
  have hsm : |Real.sqrt vt - vw - cv| ≤ (94702519 / 1000000000000000000000000000000) := by
    have hden1 : 0 < Real.sqrt vt + vw := by linarith
    have hden2 : 0 < vs + vw := by linarith
    have hid : Real.sqrt vt - vw - cv = (vt - vw * vw) * (vs - Real.sqrt vt) /
        ((Real.sqrt vt + vw) * (vs + vw)) := by
      rw [hcv]
      set u := Real.sqrt vt with hu
      rw [← hsqv]
      have h5 := hden1.ne'
      have h6 := hden2.ne'
      field_simp
      ring
    rw [hid, abs_div, abs_mul, abs_of_pos (mul_pos hden1 hden2)]
    have h3 : |vs - Real.sqrt vt| ≤ (223607 / 500000) / 2 ^ 53 := hs.2
    have h4 : ((447211 / 1000000) : ℝ) * (447211 / 1000000) ≤ (Real.sqrt vt + vw) * (vs + vw) := by
      apply mul_le_mul _ _ (by norm_num) (by linarith)
      · have : ((447211 / 1000000) : ℝ) ≤ (111803 / 500000) + (111802893 / 500000000) := by norm_num
        linarith
      · have : ((447211 / 1000000) : ℝ) ≤ ((111803 / 500000) - (223607 / 500000) / 2 ^ 53) + (111802893 / 500000000) := by norm_num
        linarith
    rw [div_le_iff₀ (mul_pos hden1 hden2)]
    have h5 := mul_le_mul htw0 h3 (abs_nonneg _) (by norm_num)
    have h6 : ((381470417 / 1000000000000000) : ℝ) * ((223607 / 500000) / 2 ^ 53) ≤ (94702519 / 1000000000000000000000000000000) * ((447211 / 1000000) * (447211 / 1000000)) := by
      norm_num
    nlinarith
  have hd : |value (0x3FE921FB54442D18 : UInt64) - ((2 * Real.sqrt vt * rv -
      (value (0x3C91A62633145C07 : UInt64) - 2 * cv)) -
        (value (0x3FE921FB54442D18 : UInt64) - 2 * vw)) - Real.arcsin a| ≤
      1 / 2 ^ 64 + 2 * ((223607 / 500000) ^ 3 * ((11 / 16) / 2 ^ 56)) + 2 * (94702519 / 1000000000000000000000000000000) := by
    rw [hy0, show value (0x3FE921FB54442D18 : UInt64) - ((2 * Real.sqrt vt * rv -
      (value (0x3C91A62633145C07 : UInt64) - 2 * cv)) -
        (value (0x3FE921FB54442D18 : UInt64) - 2 * vw)) -
          (Real.pi / 2 - 2 * Real.arcsin (Real.sqrt vt)) =
        (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2) +
          2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
            eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt))) +
          2 * (Real.sqrt vt - vw - cv) by rw [← hh4, hrv]; ring]
    have h3 := abs_add_le ((value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2) +
      2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
        eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt)))) (2 * (Real.sqrt vt - vw - cv))
    have h4 := abs_add_le (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2)
      (2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
        eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt))))
    rw [abs_mul, abs_two] at h3 h4
    have h5 : Real.sqrt vt ^ 3 * ((11 / 16) / 2 ^ 56) ≤ (223607 / 500000) ^ 3 * ((11 / 16) / 2 ^ 56) :=
      mul_le_mul_of_nonneg_right hk3 (by positivity)
    linarith
  have hB : value (UInt64.ofNat (1022 * 2 ^ 52)) = 1 / 2 := by
    rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
    norm_num
  have hyt := abs_arcsin_lt a
  refine sub_within (const_word _ hh4f) hpq (Real.arcsin a) (49 / 450359962737049600) ?_ 1022 (by norm_num)
    (by norm_num) ?_ (by norm_num) (lt_trans hyt (by norm_num))
  · norm_num at hd ⊢
    linarith
  · rw [hB, abs_of_pos (by linarith)]
    linarith

set_option maxHeartbeats 1000000 in
theorem mid_C (x : Float) (hx : Finite x.toBits) (h1 : (9 / 10) ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ (39 / 40)) (hy : 1 + (5 / 36028797018963968) ≤ Real.arcsin |value x.toBits|) :
    F64SignedRounding.WithinSteps 1 (Real.arcsin |value x.toBits|) (midTail (tOf x)).toBits := by
  obtain ⟨htf, htv⟩ := t_exact x hx (by linarith) (by linarith)
  set a := |value x.toBits| with ha
  set vt := (1 - a) / 2 with hvt
  have hvlo : (1 / 80) ≤ vt := by rw [hvt]; linarith
  have hvhi : vt ≤ (1 / 20) := by rw [hvt]; linarith
  have hvtp : 0 < vt := lt_of_lt_of_le (by norm_num) hvlo
  have ht : FSApprox (tOf x) vt vt 1 0 :=
    (fsapprox_input (tOf x) htf vt hvtp (by linarith) (by rw [htv, abs_of_pos hvtp])).congr htv
  have hr := ratio_A3 (tOf x) vt vt (ht.mono le_rfl (by norm_num)) (by linarith) hvhi hvhi
    (le_trans (by norm_num) hvlo)
  rw [ratio_eval] at hr
  obtain ⟨hrA, hrM⟩ := Log1pTheoremTail.fsapprox_abs hr hvhi
  set rv := vt * eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt with hrv
  have hrM' : |rv| ≤ (23 / 2500) := hrM.trans (le_of_eq (by norm_num))
  have hrA' := Approx.mono hrA (e' := (843 / 180143985094819840000)) (le_of_eq (by norm_num))
  -- `s = √t`
  have htA : FApprox (tOf x) vt 0 := ⟨htf, by rw [htv, sub_self, abs_zero]⟩
  have hsqrt0 : 0 < Real.sqrt vt := Real.sqrt_pos.mpr hvtp
  have hsqv : Real.sqrt vt * Real.sqrt vt = vt := Real.mul_self_sqrt hvtp.le
  have hsqhi : Real.sqrt vt ≤ (223607 / 1000000) := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hsqlo : (111803 / 1000000) ≤ Real.sqrt vt := by
    rw [Real.le_sqrt (by norm_num) hvtp.le]
    nlinarith
  have hs := Approx.mono (fapprox_sqrt htA vt vt hvtp le_rfl hvtp le_rfl (Real.sqrt vt)
    (by rw [add_zero])) (e' := (223607 / 1000000) / 2 ^ 53) (by
      rw [zero_div, zero_add]
      exact div_le_div_of_nonneg_right hsqhi (by positivity))
  set s := (tOf x).sqrt with hsd
  set vs := value s.toBits with hvs
  obtain ⟨hes1, hes2⟩ := abs_le.mp hs.2
  have hvs0 : 0 < vs := by
    have : ((223607 / 1000000) : ℝ) / 2 ^ 53 < (111803 / 1000000) := by norm_num
    linarith
  -- `w`, the high part of `s`
  have hse : 506 ≤ Wasm.IEEE64.exponent s.toBits :=
    Log1pTheoremCorr.exponent_ge _ 506 (-517) (by norm_num) (by norm_num) (by
      rw [abs_of_pos hvs0, show (2 : ℝ) ^ (-517 : ℤ) = 1 / 2 ^ 517 by norm_num]
      have : (1 : ℝ) / 2 ^ 517 ≤ (111803 / 1000000) - (223607 / 1000000) / 2 ^ 53 := by norm_num
      linarith)
  obtain ⟨hwf, hwle, hwd, q, hq, hqm⟩ := trunc_facts s.toBits hvs0 hs.1 hse
  have hwb : (wOf s).toBits = s.toBits &&& 0xFFFFFFFF00000000 := by
    unfold wOf
    rw [F64Bits.toBits_ofBits, not_nan_of_finite hwf]
    simp only [Bool.false_eq_true, ite_false]
  rw [← hwb] at hwf hwle hwd hqm
  set w := wOf s with hwdef
  set vw := value w.toBits with hvw
  have hvwlo : (111802893 / 1000000000) ≤ vw := by
    have : (111802893 / 1000000000) ≤ vs * (1 - 1 / 2 ^ 20) := by
      have h3 : ((111803 / 1000000) - (223607 / 1000000) / 2 ^ 53) * (1 - 1 / 2 ^ 20) ≤ vs * (1 - 1 / 2 ^ 20) :=
        mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
      have h4 : ((111802893 / 1000000000) : ℝ) ≤ ((111803 / 1000000) - (223607 / 1000000) / 2 ^ 53) * (1 - 1 / 2 ^ 20) := by norm_num
      linarith
    linarith
  have hvw0 : 0 < vw := lt_of_lt_of_le (by norm_num) hvwlo
  have hvwhi : vw ≤ (223607 / 1000000) + (223607 / 1000000) / 2 ^ 53 := by linarith
  -- `w * w` and `t - w * w` are exact
  have hww := F64ExactProduct.mul_exact_scaled w.toBits w.toBits hwf hwf q q
    (Wasm.IEEE64.exponent s.toBits - 1 + 32) (Wasm.IEEE64.exponent s.toBits - 1 + 32) hqm hqm
    (lt_of_le_of_lt (Nat.mul_le_mul hq.le hq.le) (by norm_num)) (by omega) (by
      have := AsinTheoremSupport.exponent_lt_one s.toBits (by
        rw [abs_of_pos hvs0]
        have : ((223607 / 1000000) : ℝ) + (223607 / 1000000) / 2 ^ 53 < 1 := by norm_num
        linarith)
      omega)
  rw [← F64Bits.toBits_mul] at hww
  have hwwv : value (w * w).toBits = vw * vw := hww.2.1
  have hwwf := hww.1
  clear hww hqm
  -- `|t - w²|` is small
  have hdw : |Real.sqrt vt - vw| ≤ (223607 / 1000000) / 2 ^ 53 + (223607 / 1000000) / 2 ^ 20 := by
    rw [abs_le]
    constructor
    · linarith
    · have : vs / 2 ^ 20 ≤ ((223607 / 1000000) + (223607 / 1000000) / 2 ^ 53) / 2 ^ 20 :=
        div_le_div_of_nonneg_right (by linarith) (by norm_num)
      have h5 : ((223607 / 1000000) + (223607 / 1000000) / 2 ^ 53 : ℝ) / 2 ^ 20 ≤ (223607 / 1000000) / 2 ^ 20 + (223607 / 1000000) / 2 ^ 53 := by
        norm_num
      linarith
  have htw0 : |vt - vw * vw| ≤ (19073521 / 200000000000000) := by
    rw [show vt - vw * vw = (Real.sqrt vt - vw) * (Real.sqrt vt + vw) by
      linear_combination (-1 : ℝ) * hsqv,
      abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt vt + vw)]
    have h3 : Real.sqrt vt + vw ≤ 2 * (223607 / 1000000) + (223607 / 1000000) / 2 ^ 53 := by linarith
    have h4 := mul_le_mul hdw h3 (by positivity) (by positivity)
    have h5 : ((223607 / 1000000) / 2 ^ 53 + (223607 / 1000000) / 2 ^ 20 : ℝ) * (2 * (223607 / 1000000) + (223607 / 1000000) / 2 ^ 53) ≤
        (19073521 / 200000000000000) := by norm_num
    linarith
  have hwwt1 : vw * vw ≤ 2 * vt := by
    have := (abs_le.mp htw0).1
    have : ((19073521 / 200000000000000) : ℝ) ≤ (1 / 80) := by norm_num
    linarith
  have hwwt2 : vt ≤ 2 * (vw * vw) := by
    have := (abs_le.mp htw0).2
    have : ((19073521 / 200000000000000) : ℝ) ≤ (1 / 80) := by norm_num
    linarith
  have htw := F64Exact.sub_exact (tOf x).toBits (w * w).toBits htf hwwf (by rw [htv]; exact hvtp)
    (by rw [hwwv]; positivity) (by rw [hwwv, htv]; exact hwwt1) (by rw [hwwv, htv]; exact hwwt2)
    (by rw [htv]; linarith [(by norm_num : ((1 / 20) : ℝ) < 2 ^ 900)])
    (by rw [hwwv]; nlinarith [(by norm_num : (4 : ℝ) < 2 ^ 900)])
  rw [← F64Bits.toBits_sub, htv, hwwv] at htw
  have htwA : FApprox (tOf x - w * w) (vt - vw * vw) 0 := ⟨htw.1, by rw [htw.2, sub_self, abs_zero]⟩
  -- `s + w` and `c`
  have hsw := fapprox_add (approx_self s.toBits hs.1) (approx_self w.toBits hwf)
    (2 * ((223607 / 1000000) + (223607 / 1000000) / 2 ^ 53)) (by
      rw [abs_of_pos (by linarith)]
      linarith) (by norm_num)
  have hsw0 : (44721 / 200000) ≤ |vs + vw| := by
    rw [abs_of_pos (by linarith)]
    have : ((44721 / 200000) : ℝ) ≤ ((111803 / 1000000) - (223607 / 1000000) / 2 ^ 53) + (111802893 / 1000000000) := by norm_num
    linarith
  have hc := fapprox_div htwA hsw (19073521 / 200000000000000) (44721 / 200000) htw0 hsw0 (by norm_num) (17060013 / 40000000000000) (by norm_num)
    (by norm_num)
  set cv := (vt - vw * vw) / (vs + vw) with hcv
  have hcM : |cv| ≤ (17060013 / 40000000000000) := by
    rw [hcv, abs_div]
    calc |vt - vw * vw| / |vs + vw| ≤ (19073521 / 200000000000000) / |vs + vw| :=
          div_le_div_of_nonneg_right htw0 (abs_nonneg _)
      _ ≤ (19073521 / 200000000000000) / (44721 / 200000) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsw0
      _ ≤ (17060013 / 40000000000000) := by norm_num
  have h2f : FApprox (2.0 : Float) 2 0 := by
    have := Log1pTheoremCore.two_approx.approx
    rw [zero_mul] at this
    exact this
  have hc2 := fapprox_mul h2f hc 2 (17060013 / 40000000000000) (by norm_num) hcM (853000651 / 1000000000000000) (by norm_num) (by norm_num)
  have hlof : Finite (0x3C91A62633145C07 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hh4f : Finite (0x3FE921FB54442D18 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hlov : |value (0x3C91A62633145C07 : UInt64)| ≤ 1 / 10 ^ 16 :=
    le_trans (abs_value_le _ ((1 / 10 ^ 16 : ℚ)) (by decide +kernel)) (by norm_num)
  have h4v : |value (0x3FE921FB54442D18 : UInt64) - 7853981633974483 / 10 ^ 16| ≤ 1 / 10 ^ 16 := by
    rw [← ratOfWord_cast, show ratOfWord 0x3FE921FB54442D18 = 884279719003555 / 2 ^ 50 by
      decide +kernel]
    norm_num [abs_le]
  have hlo2c := fapprox_sub (const_word _ hlof) hc2 (853000651 / 1000000000000000) (by
    have h3 := abs_sub (value (0x3C91A62633145C07 : UInt64)) (2 * cv)
    rw [abs_mul, abs_two] at h3
    norm_num at h3 hcM hlov ⊢
    linarith) (by norm_num)
  -- `2 s r`
  obtain ⟨h2sf, h2sv⟩ := AtanTheoremReduce.double_float s hs.1 (by
      rw [abs_of_pos hvs0]
      have : (1 : ℝ) / 2 ^ 1000 ≤ (111803 / 1000000) - (223607 / 1000000) / 2 ^ 53 := by norm_num
      linarith) (by
      rw [abs_of_pos hvs0]
      have : ((223607 / 1000000) : ℝ) + (223607 / 1000000) / 2 ^ 53 < 2 ^ 900 := by norm_num
      linarith)
  have hs2 : FApprox (2.0 * s) (2 * Real.sqrt vt) (2 * ((223607 / 1000000) / 2 ^ 53)) := by
    refine ⟨h2sf, ?_⟩
    rw [h2sv, show 2 * vs - 2 * Real.sqrt vt = 2 * (vs - Real.sqrt vt) by ring, abs_mul, abs_two]
    have := hs.2
    linarith
  have hsr := fapprox_mul hs2 hrA' (2 * (223607 / 1000000)) (23 / 2500) (by
      rw [abs_mul, abs_two, abs_of_pos hsqrt0]; linarith) hrM' (4114369 / 1000000000) (by norm_num)
    (by norm_num)
  have hp := fapprox_sub_half hsr hlo2c 1014 (by norm_num) (by
    have h3 := abs_sub (2 * Real.sqrt vt * rv) (value (0x3C91A62633145C07 : UInt64) - 2 * cv)
    have h4 : |2 * Real.sqrt vt * rv| ≤ 2 * (223607 / 1000000) * (23 / 2500) := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hsqrt0]
      exact mul_le_mul (by linarith) hrM' (abs_nonneg _) (by norm_num)
    have h5 := abs_sub (value (0x3C91A62633145C07 : UInt64)) (2 * cv)
    rw [abs_mul, abs_two] at h5
    norm_num at h3 h4 h5 hcM hlov ⊢
    linarith)
  -- `q = π/4 - 2 w`
  obtain ⟨h2wf, h2wv⟩ := AtanTheoremReduce.double_float w hwf (by
      rw [abs_of_pos hvw0]
      have : (1 : ℝ) / 2 ^ 1000 ≤ (111802893 / 1000000000) := by norm_num
      linarith) (by
      rw [abs_of_pos hvw0]
      have : ((223607 / 1000000) : ℝ) + (223607 / 1000000) / 2 ^ 53 < 2 ^ 900 := by norm_num
      linarith)
  have hw2 : FApprox (2.0 * w) (2 * vw) 0 := ⟨h2wf, by rw [h2wv, sub_self, abs_zero]⟩
  have hqb : |value (0x3FE921FB54442D18 : UInt64) - 2 * vw| ≤ (280896189 / 500000000) := by
    rw [abs_le]
    obtain ⟨h5, h6⟩ := abs_le.mp h4v
    constructor <;> norm_num at h5 h6 hvwlo hvwhi ⊢ <;> linarith
  have hq := fapprox_sub_half (const_word _ hh4f) hw2 1021 (by norm_num) (by
    norm_num at hqb ⊢
    linarith)
  have hpq := fapprox_sub_half hp hq 1021 (by norm_num) (by
    have h3 := abs_sub (2 * Real.sqrt vt * rv - (value (0x3C91A62633145C07 : UInt64) - 2 * cv))
      (value (0x3FE921FB54442D18 : UInt64) - 2 * vw)
    have h4 : |2 * Real.sqrt vt * rv| ≤ 2 * (223607 / 1000000) * (23 / 2500) := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hsqrt0]
      exact mul_le_mul (by linarith) hrM' (abs_nonneg _) (by norm_num)
    have h5 := abs_sub (value (0x3C91A62633145C07 : UInt64)) (2 * cv)
    rw [abs_mul, abs_two] at h5
    have h6 := abs_sub (2 * Real.sqrt vt * rv) (value (0x3C91A62633145C07 : UInt64) - 2 * cv)
    norm_num at h3 h4 h5 h6 hcM hlov hqb ⊢
    linarith)
  -- the exact value against `arcsin a`
  have hy0 := arcsin_half a (by linarith) (by linarith)
  rw [← hvt] at hy0
  have hker := asin_kernel (Real.sqrt vt) (by
    rw [abs_of_pos hsqrt0, Real.sqrt_le_left (by norm_num)]
    linarith)
  rw [hsqv, abs_of_pos hsqrt0] at hker
  have hpi := AtanTheoremConst.atan_inf
  have hh4 : value (0x3FE921FB54442D18 : UInt64) + value (0x3FE921FB54442D18 : UInt64) =
      value (0x3FF921FB54442D18 : UInt64) := by
    rw [← ratOfWord_cast, ← ratOfWord_cast]
    exact_mod_cast (by decide +kernel : ratOfWord 0x3FE921FB54442D18 +
      ratOfWord 0x3FE921FB54442D18 = ratOfWord 0x3FF921FB54442D18)
  have hk3 : Real.sqrt vt ^ 3 ≤ (223607 / 1000000) ^ 3 := pow_le_pow_left₀ hsqrt0.le hsqhi 3
  have hsm : |Real.sqrt vt - vw - cv| ≤ (2959467 / 62500000000000000000000000000) := by
    have hden1 : 0 < Real.sqrt vt + vw := by linarith
    have hden2 : 0 < vs + vw := by linarith
    have hid : Real.sqrt vt - vw - cv = (vt - vw * vw) * (vs - Real.sqrt vt) /
        ((Real.sqrt vt + vw) * (vs + vw)) := by
      rw [hcv]
      set u := Real.sqrt vt with hu
      rw [← hsqv]
      have h5 := hden1.ne'
      have h6 := hden2.ne'
      field_simp
      ring
    rw [hid, abs_div, abs_mul, abs_of_pos (mul_pos hden1 hden2)]
    have h3 : |vs - Real.sqrt vt| ≤ (223607 / 1000000) / 2 ^ 53 := hs.2
    have h4 : ((44721 / 200000) : ℝ) * (44721 / 200000) ≤ (Real.sqrt vt + vw) * (vs + vw) := by
      apply mul_le_mul _ _ (by norm_num) (by linarith)
      · have : ((44721 / 200000) : ℝ) ≤ (111803 / 1000000) + (111802893 / 1000000000) := by norm_num
        linarith
      · have : ((44721 / 200000) : ℝ) ≤ ((111803 / 1000000) - (223607 / 1000000) / 2 ^ 53) + (111802893 / 1000000000) := by norm_num
        linarith
    rw [div_le_iff₀ (mul_pos hden1 hden2)]
    have h5 := mul_le_mul htw0 h3 (abs_nonneg _) (by norm_num)
    have h6 : ((19073521 / 200000000000000) : ℝ) * ((223607 / 1000000) / 2 ^ 53) ≤ (2959467 / 62500000000000000000000000000) * ((44721 / 200000) * (44721 / 200000)) := by
      norm_num
    nlinarith
  have hd : |value (0x3FE921FB54442D18 : UInt64) - ((2 * Real.sqrt vt * rv -
      (value (0x3C91A62633145C07 : UInt64) - 2 * cv)) -
        (value (0x3FE921FB54442D18 : UInt64) - 2 * vw)) - Real.arcsin a| ≤
      1 / 2 ^ 64 + 2 * ((223607 / 1000000) ^ 3 * ((11 / 16) / 2 ^ 56)) + 2 * (2959467 / 62500000000000000000000000000) := by
    rw [hy0, show value (0x3FE921FB54442D18 : UInt64) - ((2 * Real.sqrt vt * rv -
      (value (0x3C91A62633145C07 : UInt64) - 2 * cv)) -
        (value (0x3FE921FB54442D18 : UInt64) - 2 * vw)) -
          (Real.pi / 2 - 2 * Real.arcsin (Real.sqrt vt)) =
        (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2) +
          2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
            eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt))) +
          2 * (Real.sqrt vt - vw - cv) by rw [← hh4, hrv]; ring]
    have h3 := abs_add_le ((value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2) +
      2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
        eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt)))) (2 * (Real.sqrt vt - vw - cv))
    have h4 := abs_add_le (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2)
      (2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
        eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt))))
    rw [abs_mul, abs_two] at h3 h4
    have h5 : Real.sqrt vt ^ 3 * ((11 / 16) / 2 ^ 56) ≤ (223607 / 1000000) ^ 3 * ((11 / 16) / 2 ^ 56) :=
      mul_le_mul_of_nonneg_right hk3 (by positivity)
    linarith
  have hB : value (UInt64.ofNat (1023 * 2 ^ 52)) = 1 := by
    rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]
    norm_num
  have hyt := abs_arcsin_lt a
  refine sub_within (const_word _ hh4f) hpq (Real.arcsin a) (5 / 36028797018963968) ?_ 1023 (by norm_num)
    (by norm_num) ?_ (by norm_num) (lt_trans hyt (by norm_num))
  · norm_num at hd ⊢
    linarith
  · rw [hB, abs_of_pos (by linarith)]
    linarith

end Verified.Examples.AsinTheoremMid
