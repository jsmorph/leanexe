import Verified.Examples.AsinTheoremHalf

/-!
`Asin.asin x` for `0.974998 ≤ |x| < 1`: `π/2 - 2 (s + s r)` with `t = (1 - |x|)/2 ≤ 1/79`,
`s = √t`, and `r = asinRatio t`, against `arcsin |x| = π/2 - 2 arcsin √t`.  The result lies in
`[1.35, π/2]`, where one spacing is `2 ^ -52`, and every term before the last difference is below
`0.23`, so relative bounds on each operation suffice.
-/

namespace Verified.Examples.AsinTheoremBig
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest PolyBound AsinTheoremSupport
  AsinTheoremRatio AsinTheoremBranches AsinTheoremSmall AsinTheoremHalf

set_option exponentiation.threshold 4096

theorem const_word (w : UInt64) (hw : Finite w) : FApprox (Float.ofBits w) (value w) 0 :=
  fapprox_ofBits w hw

theorem big_within (x : Float) (hx : Finite x.toBits) (h1 : 974998 / 1000000 ≤ |value x.toBits|)
    (h2 : |value x.toBits| < 1) :
    F64SignedRounding.WithinSteps 1 (Real.arcsin |value x.toBits|) (bigTail (tOf x)).toBits := by
  obtain ⟨htf, htv⟩ := t_exact x hx (by linarith) h2
  have hge := one_sub_ge x hx (by linarith) h2
  set a := |value x.toBits| with ha
  set vt := (1 - a) / 2 with hvt
  have hvt0 : 1 / 2 ^ 54 ≤ vt := by rw [hvt]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 54 = 1 / 2 ^ 53 / 2)]
  have hvt1 : vt ≤ 1 / 79 := by rw [hvt]; linarith
  have hvtp : 0 < vt := lt_of_lt_of_le (by positivity) hvt0
  have ht : FSApprox (tOf x) vt vt 1 0 :=
    (fsapprox_input (tOf x) htf vt hvtp (by linarith) (by rw [htv, abs_of_pos hvtp])).congr htv
  have hr := ratio_A4 (tOf x) vt vt (ht.mono le_rfl (by norm_num)) hvtp.le hvt1 hvt1 (le_trans (by norm_num) hvt0)
  rw [ratio_eval] at hr
  obtain ⟨hrA, hrM⟩ := Log1pTheoremTail.fsapprox_abs hr (le_refl vt)
  set rv := vt * eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt with hrv
  -- `s = √t`
  have htA : FApprox (tOf x) vt 0 := ⟨htf, by rw [htv, sub_self, abs_zero]⟩
  have hsq := fapprox_sqrt htA vt vt hvtp le_rfl hvtp le_rfl (Real.sqrt vt) (by rw [add_zero])
  have hsqrt0 : 0 < Real.sqrt vt := Real.sqrt_pos.mpr hvtp
  have hsqrt1 : Real.sqrt vt ≤ 1126 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
    linarith
  have hs := Approx.mono hsq (e' := (1126 / 10000) / 2 ^ 53) (by
    rw [zero_div, zero_add]
    exact div_le_div_of_nonneg_right hsqrt1 (by positivity))
  -- `s r`
  have hMr : |rv| ≤ 1719 / 10000 * (1 / 79) := hrM.trans (by nlinarith)
  have her : 891 / 1250 / 2 ^ 53 * vt ≤ 891 / 1250 / 2 ^ 53 * (1 / 79) :=
    mul_le_mul_of_nonneg_left hvt1 (by positivity)
  have hrA' := Approx.mono hrA (e' := 891 / 1250 / 2 ^ 53 * (1 / 79)) her
  have hsr := fapprox_mul hs hrA' (1126 / 10000) (1719 / 10000 * (1 / 79))
    (by rw [abs_of_pos hsqrt0]; exact hsqrt1) hMr (1 / 400) (by norm_num) (by norm_num)
  -- `s + s r`
  have hssr := fapprox_add hs hsr (115 / 1000) (by
    have h3 : |Real.sqrt vt * rv| ≤ 1126 / 10000 * (1719 / 10000 * (1 / 79)) := by
      rw [abs_mul, abs_of_pos hsqrt0]
      exact mul_le_mul hsqrt1 hMr (abs_nonneg _) (by norm_num)
    have := abs_add_le (Real.sqrt vt) (Real.sqrt vt * rv)
    rw [abs_of_pos hsqrt0] at this
    norm_num at h3 this ⊢
    linarith) (by norm_num)
  -- `2 (s + s r)` is exact
  set ssr := (tOf x).sqrt + (tOf x).sqrt * Asin.asinRatio (tOf x) with hssrd
  have hlo := hssr.lower
  have hhi := hssr.upper
  have hrv0 : |Real.sqrt vt * rv| ≤ 1126 / 10000 * (1719 / 10000 * (1 / 79)) := by
    rw [abs_mul, abs_of_pos hsqrt0]
    exact mul_le_mul hsqrt1 hMr (abs_nonneg _) (by norm_num)
  have hsq0 : 1 / 2 ^ 27 ≤ Real.sqrt vt := by
    rw [Real.le_sqrt (by positivity) hvtp.le]
    norm_num
    linarith
  have hev : (1126 / 10000) / 2 ^ 53 + ((1126 / 10000) / 2 ^ 53 * (1719 / 10000 * (1 / 79)) +
      1126 / 10000 * (891 / 1250 / 2 ^ 53 * (1 / 79)) + (1126 / 10000) / 2 ^ 53 *
        (891 / 1250 / 2 ^ 53 * (1 / 79)) + 1 / 400 / 2 ^ 53 + 1 / 2 ^ 1075) +
      115 / 1000 / 2 ^ 53 ≤ (23 / 100) / 2 ^ 53 := by norm_num
  have hv1 : 1 / 2 ^ 1000 ≤ |value ssr.toBits| := by
    have := (abs_le.mp hrv0).1
    rw [abs_of_pos (by norm_num at hlo this hev ⊢; nlinarith)]
    norm_num at hlo this hev hsq0 ⊢
    linarith
  have hv2 : |value ssr.toBits| < 2 ^ 900 := by
    have := (abs_le.mp hrv0).2
    rw [abs_lt]
    norm_num at hlo hhi this hev hsqrt1 ⊢
    constructor <;> linarith
  obtain ⟨h2f, h2v⟩ := AtanTheoremReduce.double_float ssr hssr.1 hv1 hv2
  have htwo : FApprox (2.0 * ssr) (2 * (Real.sqrt vt + Real.sqrt vt * rv)) ((46 / 100) / 2 ^ 53) := by
    refine ⟨h2f, ?_⟩
    rw [h2v, show 2 * value ssr.toBits - 2 * (Real.sqrt vt + Real.sqrt vt * rv) =
      2 * (value ssr.toBits - (Real.sqrt vt + Real.sqrt vt * rv)) by ring, abs_mul, abs_two]
    have := hssr.2
    linarith
  -- `2 (s + s r) - pio2_lo`
  have hlof : Finite (0x3C91A62633145C07 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hhif : Finite (0x3FF921FB54442D18 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hlov : |value (0x3C91A62633145C07 : UInt64)| ≤ 1 / 10 ^ 16 :=
    le_trans (abs_value_le _ ((1 / 10 ^ 16 : ℚ)) (by decide +kernel)) (by norm_num)
  have hm := fapprox_sub htwo (const_word _ hlof) (24 / 100) (by
    have h3 := abs_sub (2 * (Real.sqrt vt + Real.sqrt vt * rv)) (value 0x3C91A62633145C07)
    have h4 : |2 * (Real.sqrt vt + Real.sqrt vt * rv)| ≤ 2 * (1126 / 10000 + 1126 / 10000 *
        (1719 / 10000 * (1 / 79))) := by
      rw [abs_mul, abs_two]
      have := abs_add_le (Real.sqrt vt) (Real.sqrt vt * rv)
      rw [abs_of_pos hsqrt0] at this
      linarith
    norm_num at h3 h4 hlov ⊢
    linarith) (by norm_num)
  -- the exact value against `arcsin a`
  have hy := arcsin_half a (by linarith) (by linarith)
  rw [← hvt] at hy
  have hker := asin_kernel (Real.sqrt vt) (by rw [abs_of_pos hsqrt0]; linarith)
  rw [Real.mul_self_sqrt hvtp.le, abs_of_pos hsqrt0] at hker
  have hpi := AtanTheoremConst.atan_inf
  have hk3 : Real.sqrt vt ^ 3 ≤ (1126 / 10000) ^ 3 := pow_le_pow_left₀ hsqrt0.le hsqrt1 3
  have hd : |value 0x3FF921FB54442D18 - (2 * (Real.sqrt vt + Real.sqrt vt * rv) -
      value 0x3C91A62633145C07) - Real.arcsin a| ≤ 1 / 2 ^ 64 + 2 * ((1126 / 10000) ^ 3 *
        ((11 / 16) / 2 ^ 56)) := by
    rw [hy, show value 0x3FF921FB54442D18 - (2 * (Real.sqrt vt + Real.sqrt vt * rv) -
      value 0x3C91A62633145C07) - (Real.pi / 2 - 2 * Real.arcsin (Real.sqrt vt)) =
        (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2) +
          2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
            eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt))) by rw [hrv]; ring]
    have h3 := abs_add_le (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2)
      (2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
        eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt))))
    rw [abs_mul, abs_two] at h3
    have h4 : Real.sqrt vt ^ 3 * ((11 / 16) / 2 ^ 56) ≤ (1126 / 10000) ^ 3 * ((11 / 16) / 2 ^ 56) :=
      mul_le_mul_of_nonneg_right hk3 (by positivity)
    linarith
  -- `arcsin a ≥ 1.34`
  have hya : 134 / 100 ≤ Real.arcsin a := by
    rw [hy]
    have h3 := (abs_le.mp hker).2
    have h4 := (abs_le.mp hrv0).2
    have h5 := Real.pi_gt_d2
    rw [← hrv] at h3
    norm_num at h3 h4 ⊢
    nlinarith
  have hB : value (UInt64.ofNat (1023 * 2 ^ 52)) = 1 := by
    rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]
    norm_num
  refine sub_within (const_word _ hhif) hm (Real.arcsin a) (1 / 2 ^ 53) ?_ 1023 (by norm_num)
    (by norm_num) ?_ (by norm_num) ?_
  · norm_num at hd ⊢
    linarith
  · rw [hB, abs_of_pos (by linarith)]
    norm_num
    linarith
  · rw [abs_lt]
    have := Real.arcsin_le_pi_div_two a
    have := Real.pi_lt_four
    constructor <;> nlinarith [(by norm_num : (2 : ℝ) < 2 ^ 1022)]

#print axioms big_within

end Verified.Examples.AsinTheoremBig
