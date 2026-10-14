import Verified.Examples.TgammaDD
import Verified.Examples.TgammaFloor

/-!
`Tgamma.mulDD3`, the product of two double-doubles in the accurate path of `Tgamma`: the rounded
product `ch = xh yh`, its error `fma xh yh (-ch)`, the three cross terms summed in double
arithmetic, and a final `fastTwoSum`.  For low parts at most `2 ^ -50` of their high parts and a
product `P = xh yh` with `2 ^ -900 ≤ |P| ≤ 2 ^ 899`, the result lies within `2 ^ -98 |P|` of
`(xh + xl) (yh + yl)`, and its low part is at most `2 ^ -51` of its high part (`mulDD3_spec`).
For low parts up to `2 ^ -30` of their high parts the bound is `2 ^ -78 |P|` (`mulDD3_wide`).
-/

namespace Verified.Examples.TgammaMulDD3
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD

set_option exponentiation.threshold 4096

/-- **The double-double product `mulDD3`.** -/
theorem mulDD3_spec (hF : FmaSpec.FmaNearest) (xh xl yh yl : Float) (hxh : Finite xh.toBits)
    (hxl : Finite xl.toBits) (hyh : Finite yh.toBits) (hyl : Finite yl.toBits)
    (hxlb : |value xl.toBits| ≤ |value xh.toBits| / 2 ^ 50)
    (hylb : |value yl.toBits| ≤ |value yh.toBits| / 2 ^ 50)
    (hP : 1 / 2 ^ 900 ≤ |value xh.toBits| * |value yh.toBits|)
    (hPmax : |value xh.toBits| * |value yh.toBits| ≤ 2 ^ 899) :
    Finite (mulDD3 xh xl yh yl).1.toBits ∧ Finite (mulDD3 xh xl yh yl).2.toBits ∧
      |value (mulDD3 xh xl yh yl).1.toBits + value (mulDD3 xh xl yh yl).2.toBits -
          (value xh.toBits + value xl.toBits) * (value yh.toBits + value yl.toBits)| ≤
        |value xh.toBits| * |value yh.toBits| / 2 ^ 98 ∧
      |value (mulDD3 xh xl yh yl).2.toBits| ≤ |value (mulDD3 xh xl yh yl).1.toBits| / 2 ^ 51 ∧
      |value (mulDD3 xh xl yh yl).1.toBits| ≤ 2 * (|value xh.toBits| * |value yh.toBits|) ∧
      |value xh.toBits| * |value yh.toBits| / 2 ≤ |value (mulDD3 xh xl yh yl).1.toBits| := by
  set a := value xh.toBits with ha
  set b := value xl.toBits with hb
  set c := value yh.toBits with hc
  set e := value yl.toBits with he
  set P := |a| * |c| with hPdef
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have htiny : (1 : ℝ) / 2 ^ 1075 ≤ P / 2 ^ 170 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 : ℝ) / 2 ^ 900 * 2 ^ 1075 ≤ P * 2 ^ 1075 :=
      mul_le_mul_of_nonneg_right hP (by positivity)
    nlinarith [(by norm_num : (1 : ℝ) * 2 ^ 170 ≤ 1 / 2 ^ 900 * 2 ^ 1075)]
  have hb0 := abs_nonneg b
  have he0 := abs_nonneg e
  -- `ch = xh yh`
  have hch := fapprox_mul (fapprox_self xh hxh) (fapprox_self yh hyh) |a| |c| le_rfl le_rfl P
    (by simp [hPdef]) (by linarith [(by norm_num : (2 : ℝ) ^ 899 < 2 ^ 1022)])
  have hche : |value (xh * yh).toBits - a * c| ≤ P / 2 ^ 53 + 1 / 2 ^ 1075 := by
    have h := hch.2
    simp only [zero_mul, mul_zero, add_zero, zero_add] at h
    exact h
  -- `cl1 = fma xh yh (-ch)`, the error of `ch`
  obtain ⟨hnf, hnv⟩ := TgammaFloor.neg_float _ hch.1
  have hS1 : |a * c - value (xh * yh).toBits| ≤ P / 2 ^ 52 := by
    rw [abs_sub_comm]
    have h170 : P / 2 ^ 170 ≤ P / 2 ^ 53 := div_le_div_of_nonneg_left hP0.le (by positivity)
      (by norm_num)
    have e : P / 2 ^ 53 + P / 2 ^ 53 = P / 2 ^ 52 := by ring
    linarith
  have hcl1 := fma_approx hF xh yh (-(xh * yh)) hxh hyh hnf (by
    rw [hnv, ← sub_eq_add_neg]
    linarith [div_le_self hP0.le (by norm_num : (1 : ℝ) ≤ 2 ^ 52)])
  rw [hnv, ← sub_eq_add_neg] at hcl1
  have hcl1e : |value (Fma.fma xh yh (-(xh * yh))).toBits - (a * c - value (xh * yh).toBits)| ≤
      P / 2 ^ 104 := by
    have h := hcl1.2
    have : |a * c - value (xh * yh).toBits| / 2 ^ 53 ≤ P / 2 ^ 52 / 2 ^ 53 :=
      div_le_div_of_nonneg_right hS1 (by norm_num)
    have e2 : P / 2 ^ 52 / 2 ^ 53 = P / 2 ^ 105 := by ring
    have : P / 2 ^ 170 ≤ P / 2 ^ 105 := div_le_div_of_nonneg_left hP0.le (by positivity)
      (by norm_num)
    have e3 : P / 2 ^ 105 + P / 2 ^ 105 = P / 2 ^ 104 := by ring
    linarith
  -- the cross terms
  have hxe : |a| * |e| ≤ P / 2 ^ 50 := by
    calc |a| * |e| ≤ |a| * (|c| / 2 ^ 50) := mul_le_mul_of_nonneg_left hylb (abs_nonneg _)
      _ = P / 2 ^ 50 := by rw [hPdef]; ring
  have hbc : |b| * |c| ≤ P / 2 ^ 50 := by
    calc |b| * |c| ≤ |a| / 2 ^ 50 * |c| := mul_le_mul_of_nonneg_right hxlb (abs_nonneg _)
      _ = P / 2 ^ 50 := by rw [hPdef]; ring
  have hbe : |b| * |e| ≤ P / 2 ^ 100 := by
    calc |b| * |e| ≤ |a| / 2 ^ 50 * (|c| / 2 ^ 50) := mul_le_mul hxlb hylb he0 (by positivity)
      _ = P / 2 ^ 100 := by rw [hPdef]; ring
  have hPm : P / 2 ^ 49 < 2 ^ 1022 := by
    have : P / 2 ^ 49 ≤ P := div_le_self hP0.le (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 899 < 2 ^ 1022)]
  have ht0 := fapprox_mul (fapprox_self xl hxl) (fapprox_self yl hyl) |b| |e| le_rfl le_rfl
    (P / 2 ^ 100) (by simp only [add_zero]; exact hbe) (by
      have : P / 2 ^ 100 ≤ P / 2 ^ 49 := div_le_div_of_nonneg_left hP0.le (by positivity)
        (by norm_num)
      linarith)
  have hm1 := fapprox_mul (fapprox_self xh hxh) (fapprox_self yl hyl) |a| |e| le_rfl le_rfl
    (P / 2 ^ 50) (by simp only [add_zero]; exact hxe) (by
      have : P / 2 ^ 50 ≤ P / 2 ^ 49 := div_le_div_of_nonneg_left hP0.le (by positivity)
        (by norm_num)
      linarith)
  have hm2 := fapprox_mul (fapprox_self xl hxl) (fapprox_self yh hyh) |b| |c| le_rfl le_rfl
    (P / 2 ^ 50) (by simp only [add_zero]; exact hbc) (by
      have : P / 2 ^ 50 ≤ P / 2 ^ 49 := div_le_div_of_nonneg_left hP0.le (by positivity)
        (by norm_num)
      linarith)
  simp only [zero_mul, mul_zero, add_zero, zero_add] at ht0 hm1 hm2
  -- `tl1 = xl yl + xh yl`
  have htl1 := fapprox_add ht0 hm1 (P * (1 / 2 ^ 49)) (by
      have h1 := abs_add_le (b * e) (a * e)
      rw [abs_mul, abs_mul] at h1
      have h2 : P / 2 ^ 100 / 2 ^ 53 + 1 / 2 ^ 1075 + (P / 2 ^ 50 / 2 ^ 53 + 1 / 2 ^ 1075) ≤
          P / 2 ^ 100 := by
        have e2 : P / 2 ^ 100 / 2 ^ 53 + P / 2 ^ 170 + (P / 2 ^ 50 / 2 ^ 53 + P / 2 ^ 170) =
            P * (1 / 2 ^ 153 + 2 / 2 ^ 170 + 1 / 2 ^ 103) := by ring
        have : P * (1 / 2 ^ 153 + 2 / 2 ^ 170 + 1 / 2 ^ 103) ≤ P * (1 / 2 ^ 100) :=
          mul_le_mul_of_nonneg_left (by norm_num) hP0.le
        have e3 : P * (1 / 2 ^ 100) = P / 2 ^ 100 := by ring
        linarith
      have e4 : P * (1 / 2 ^ 49) = P / 2 ^ 50 + P / 2 ^ 50 := by ring
      have : P / 2 ^ 100 + P / 2 ^ 100 ≤ P / 2 ^ 50 := by
        have e5 : P / 2 ^ 100 + P / 2 ^ 100 = P * (2 / 2 ^ 100) := by ring
        have e6 : P / 2 ^ 50 = P * (1 / 2 ^ 50) := by ring
        rw [e5, e6]; exact mul_le_mul_of_nonneg_left (by norm_num) hP0.le
      linarith) (by
      have : P * (1 / 2 ^ 49) ≤ P := by
        have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 49 ≤ 1) hP0.le
        linarith
      linarith [(by norm_num : (2 : ℝ) ^ 899 < 2 ^ 1023)])
  -- `cl2 = tl1 + xl yh`
  have hcl2 := fapprox_add htl1 hm2 (P * (1 / 2 ^ 48)) (by
      have h1 := abs_add_le (b * e + a * e) (b * c)
      have h1' := abs_add_le (b * e) (a * e)
      rw [abs_mul, abs_mul] at h1'
      rw [abs_mul] at h1
      have e2 : P / 2 ^ 100 / 2 ^ 53 + P / 2 ^ 170 + (P / 2 ^ 50 / 2 ^ 53 + P / 2 ^ 170) +
          P * (1 / 2 ^ 49) / 2 ^ 53 + (P / 2 ^ 50 / 2 ^ 53 + P / 2 ^ 170) + P / 2 ^ 100 +
          P / 2 ^ 50 + P / 2 ^ 50 ≤ P * (1 / 2 ^ 48) := by
        have e3 : P / 2 ^ 100 / 2 ^ 53 + P / 2 ^ 170 + (P / 2 ^ 50 / 2 ^ 53 + P / 2 ^ 170) +
            P * (1 / 2 ^ 49) / 2 ^ 53 + (P / 2 ^ 50 / 2 ^ 53 + P / 2 ^ 170) + P / 2 ^ 100 +
            P / 2 ^ 50 + P / 2 ^ 50 = P * (1 / 2 ^ 153 + 3 / 2 ^ 170 + 2 / 2 ^ 103 +
              1 / 2 ^ 102 + 1 / 2 ^ 100 + 2 / 2 ^ 50) := by ring
        rw [e3]; exact mul_le_mul_of_nonneg_left (by norm_num) hP0.le
      linarith) (by
      have : P * (1 / 2 ^ 48) ≤ P := by
        have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 48 ≤ 1) hP0.le
        linarith
      linarith [(by norm_num : (2 : ℝ) ^ 899 < 2 ^ 1023)])
  -- `cl3 = cl1 + cl2`
  have hcl3 := fapprox_add hcl1 hcl2 (P * (1 / 2 ^ 47)) (by
      have h1 := abs_add_le (a * c - value (xh * yh).toBits) (b * e + a * e + b * c)
      have h2 := abs_add_le (b * e + a * e) (b * c)
      have h3 := abs_add_le (b * e) (a * e)
      rw [abs_mul] at h2
      rw [abs_mul, abs_mul] at h3
      have e2 : P / 2 ^ 52 + (P / 2 ^ 100 + P / 2 ^ 50 + P / 2 ^ 50) +
          (|a * c - value (xh * yh).toBits| / 2 ^ 53 + 1 / 2 ^ 1075 +
            (P / 2 ^ 100 / 2 ^ 53 + 1 / 2 ^ 1075 + (P / 2 ^ 50 / 2 ^ 53 + 1 / 2 ^ 1075) +
              P * (1 / 2 ^ 49) / 2 ^ 53 + (P / 2 ^ 50 / 2 ^ 53 + 1 / 2 ^ 1075) +
              P * (1 / 2 ^ 48) / 2 ^ 53)) ≤ P * (1 / 2 ^ 47) := by
        have h4 : |a * c - value (xh * yh).toBits| / 2 ^ 53 ≤ P / 2 ^ 52 / 2 ^ 53 :=
          div_le_div_of_nonneg_right hS1 (by norm_num)
        have e3 : P / 2 ^ 52 + (P / 2 ^ 100 + P / 2 ^ 50 + P / 2 ^ 50) +
            (P / 2 ^ 52 / 2 ^ 53 + P / 2 ^ 170 +
              (P / 2 ^ 100 / 2 ^ 53 + P / 2 ^ 170 + (P / 2 ^ 50 / 2 ^ 53 + P / 2 ^ 170) +
                P * (1 / 2 ^ 49) / 2 ^ 53 + (P / 2 ^ 50 / 2 ^ 53 + P / 2 ^ 170) +
                P * (1 / 2 ^ 48) / 2 ^ 53)) =
            P * (1 / 2 ^ 52 + 1 / 2 ^ 100 + 2 / 2 ^ 50 + 1 / 2 ^ 105 + 4 / 2 ^ 170 +
              1 / 2 ^ 153 + 2 / 2 ^ 103 + 1 / 2 ^ 102 + 1 / 2 ^ 101) := by ring
        have : P * (1 / 2 ^ 52 + 1 / 2 ^ 100 + 2 / 2 ^ 50 + 1 / 2 ^ 105 + 4 / 2 ^ 170 +
            1 / 2 ^ 153 + 2 / 2 ^ 103 + 1 / 2 ^ 102 + 1 / 2 ^ 101) ≤ P * (1 / 2 ^ 47) :=
          mul_le_mul_of_nonneg_left (by norm_num) hP0.le
        linarith
      linarith) (by
      have : P * (1 / 2 ^ 47) ≤ P := by
        have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 47 ≤ 1) hP0.le
        linarith
      linarith [(by norm_num : (2 : ℝ) ^ 899 < 2 ^ 1023)])
  set cl3 := Fma.fma xh yh (-(xh * yh)) + (xl * yl + xh * yl + xl * yh) with hcl3d
  set ch := xh * yh with hchd
  have hE : |value cl3.toBits - (a * c - value ch.toBits + (b * e + a * e + b * c))| ≤
      P / 2 ^ 98 - P / 2 ^ 120 := by
    have h := hcl3.2
    have h4 : |a * c - value ch.toBits| / 2 ^ 53 ≤ P / 2 ^ 52 / 2 ^ 53 :=
      div_le_div_of_nonneg_right hS1 (by norm_num)
    have e3 : P / 2 ^ 52 / 2 ^ 53 + P / 2 ^ 170 +
        (P / 2 ^ 100 / 2 ^ 53 + P / 2 ^ 170 + (P / 2 ^ 50 / 2 ^ 53 + P / 2 ^ 170) +
          P * (1 / 2 ^ 49) / 2 ^ 53 + (P / 2 ^ 50 / 2 ^ 53 + P / 2 ^ 170) +
          P * (1 / 2 ^ 48) / 2 ^ 53) + P * (1 / 2 ^ 47) / 2 ^ 53 =
        P * (1 / 2 ^ 105 + 4 / 2 ^ 170 + 1 / 2 ^ 153 + 2 / 2 ^ 103 + 1 / 2 ^ 102 + 1 / 2 ^ 101 +
          1 / 2 ^ 100) := by ring
    have h5 : P * (1 / 2 ^ 105 + 4 / 2 ^ 170 + 1 / 2 ^ 153 + 2 / 2 ^ 103 + 1 / 2 ^ 102 +
        1 / 2 ^ 101 + 1 / 2 ^ 100) ≤ P * (1 / 2 ^ 98 - 1 / 2 ^ 120) :=
      mul_le_mul_of_nonneg_left (by norm_num) hP0.le
    have e4 : P * (1 / 2 ^ 98 - 1 / 2 ^ 120) = P / 2 ^ 98 - P / 2 ^ 120 := by ring
    linarith
  have hcl3b : |value cl3.toBits| ≤ P / 2 ^ 46 := by
    have h1 := abs_sub_abs_le_abs_sub (value cl3.toBits)
      (a * c - value ch.toBits + (b * e + a * e + b * c))
    have h2 := abs_add_le (a * c - value ch.toBits) (b * e + a * e + b * c)
    have h3 := abs_add_le (b * e + a * e) (b * c)
    have h4 := abs_add_le (b * e) (a * e)
    rw [abs_mul] at h3
    rw [abs_mul, abs_mul] at h4
    have e5 : P / 2 ^ 98 + P / 2 ^ 52 + (P / 2 ^ 100 + P / 2 ^ 50 + P / 2 ^ 50) ≤ P / 2 ^ 46 := by
      have e6 : P / 2 ^ 98 + P / 2 ^ 52 + (P / 2 ^ 100 + P / 2 ^ 50 + P / 2 ^ 50) =
          P * (1 / 2 ^ 98 + 1 / 2 ^ 52 + 1 / 2 ^ 100 + 2 / 2 ^ 50) := by ring
      have e7 : P / 2 ^ 46 = P * (1 / 2 ^ 46) := by ring
      rw [e6, e7]; exact mul_le_mul_of_nonneg_left (by norm_num) hP0.le
    have : 0 ≤ P / 2 ^ 120 := by positivity
    linarith
  have hchb1 : P - P / 2 ^ 52 ≤ |value ch.toBits| := by
    have := abs_sub_abs_le_abs_sub (a * c) (value ch.toBits)
    rw [abs_mul] at this
    linarith
  have hchb2 : |value ch.toBits| ≤ P + P / 2 ^ 52 := by
    have := abs_sub_abs_le_abs_sub (value ch.toBits) (a * c)
    rw [abs_mul] at this
    rw [abs_sub_comm] at hS1
    linarith
  have hord : |value cl3.toBits| ≤ |value ch.toBits| := by
    have : P / 2 ^ 46 + P / 2 ^ 52 ≤ P := by
      have e6 : P / 2 ^ 46 + P / 2 ^ 52 = P * (1 / 2 ^ 46 + 1 / 2 ^ 52) := by ring
      rw [e6]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 46 + 1 / 2 ^ 52 ≤ 1) hP0.le
      linarith
    linarith
  obtain ⟨hhf, hlf, hsum, hlt, hlb⟩ := fastTwoSum_spec ch cl3 hch.1 hcl3.1 hord
    (by linarith [(by norm_num : (2 : ℝ) ^ 899 + 2 ^ 899 / 2 ^ 52 < 2 ^ 900),
      div_le_div_of_nonneg_right hPmax (by norm_num : (0 : ℝ) ≤ 2 ^ 52)])
  have hmd : mulDD3 xh xl yh yl = fastTwoSum ch cl3 := rfl
  rw [hmd]
  have hhi1 : |value (fastTwoSum ch cl3).1.toBits| ≤ 2 * P := by
    have h1 := abs_sub_abs_le_abs_sub (value (fastTwoSum ch cl3).1.toBits)
      (-(value (fastTwoSum ch cl3).2.toBits))
    rw [sub_neg_eq_add, abs_neg, hsum] at h1
    have h2 := abs_add_le (value ch.toBits) (value cl3.toBits)
    have : P / 2 ^ 52 + 2 * (P / 2 ^ 46) ≤ P := by
      have e6 : P / 2 ^ 52 + 2 * (P / 2 ^ 46) = P * (1 / 2 ^ 52 + 2 / 2 ^ 46) := by ring
      rw [e6]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 52 + 2 / 2 ^ 46 ≤ 1) hP0.le
      linarith
    linarith
  have hhi2 : P / 2 ≤ |value (fastTwoSum ch cl3).1.toBits| := by
    have h1 := abs_sub_abs_le_abs_sub (value (fastTwoSum ch cl3).1.toBits +
      value (fastTwoSum ch cl3).2.toBits) (value (fastTwoSum ch cl3).2.toBits)
    rw [add_sub_cancel_right, hsum] at h1
    have h2 := abs_sub_abs_le_abs_sub (value ch.toBits) (-(value cl3.toBits))
    rw [sub_neg_eq_add, abs_neg] at h2
    have : P / 2 ^ 52 + 2 * (P / 2 ^ 46) ≤ P / 2 := by
      have e6 : P / 2 ^ 52 + 2 * (P / 2 ^ 46) = P * (1 / 2 ^ 52 + 2 / 2 ^ 46) := by ring
      have e7 : P / 2 = P * (1 / 2) := by ring
      rw [e6, e7]
      exact mul_le_mul_of_nonneg_left (by norm_num) hP0.le
    linarith
  refine ⟨hhf, hlf, ?_, ?_, hhi1, hhi2⟩
  · rw [hsum]
    have e : value ch.toBits + value cl3.toBits - (a + b) * (c + e) =
        value cl3.toBits - (a * c - value ch.toBits + (b * e + a * e + b * c)) := by ring
    rw [e]
    have : 0 ≤ P / 2 ^ 120 := by positivity
    linarith
  · refine hlb.trans ?_
    have : (1 : ℝ) / 2 ^ 1074 ≤ |value (fastTwoSum ch cl3).1.toBits| / 2 ^ 52 := by
      rw [le_div_iff₀ (by positivity)]
      have : P / 2 ≥ 1 / 2 ^ 901 := by linarith
      nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 * 2 ^ 52 ≤ 1 / 2 ^ 901)]
    have e6 : |value (fastTwoSum ch cl3).1.toBits| / 2 ^ 52 + |value (fastTwoSum ch cl3).1.toBits| /
        2 ^ 52 = |value (fastTwoSum ch cl3).1.toBits| / 2 ^ 51 := by ring
    linarith

/-- **The double-double product `mulDD3`** for low parts up to `2 ^ -30` of their high parts. -/
theorem mulDD3_wide (hF : FmaSpec.FmaNearest) (xh xl yh yl : Float) (hxh : Finite xh.toBits)
    (hxl : Finite xl.toBits) (hyh : Finite yh.toBits) (hyl : Finite yl.toBits)
    (hxlb : |value xl.toBits| ≤ |value xh.toBits| / 2 ^ 30)
    (hylb : |value yl.toBits| ≤ |value yh.toBits| / 2 ^ 30)
    (hP : 1 / 2 ^ 900 ≤ |value xh.toBits| * |value yh.toBits|)
    (hPmax : |value xh.toBits| * |value yh.toBits| ≤ 2 ^ 899) :
    Finite (mulDD3 xh xl yh yl).1.toBits ∧ Finite (mulDD3 xh xl yh yl).2.toBits ∧
      |value (mulDD3 xh xl yh yl).1.toBits + value (mulDD3 xh xl yh yl).2.toBits -
          (value xh.toBits + value xl.toBits) * (value yh.toBits + value yl.toBits)| ≤
        |value xh.toBits| * |value yh.toBits| / 2 ^ 78 ∧
      |value (mulDD3 xh xl yh yl).2.toBits| ≤ |value (mulDD3 xh xl yh yl).1.toBits| / 2 ^ 51 ∧
      |value (mulDD3 xh xl yh yl).1.toBits| ≤ 2 * (|value xh.toBits| * |value yh.toBits|) ∧
      |value xh.toBits| * |value yh.toBits| / 2 ≤ |value (mulDD3 xh xl yh yl).1.toBits| := by
  set a := value xh.toBits with ha
  set b := value xl.toBits with hb
  set c := value yh.toBits with hc
  set e := value yl.toBits with he
  set P := |a| * |c| with hPdef
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have htiny : (1 : ℝ) / 2 ^ 1075 ≤ P / 2 ^ 170 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 : ℝ) / 2 ^ 900 * 2 ^ 1075 ≤ P * 2 ^ 1075 :=
      mul_le_mul_of_nonneg_right hP (by positivity)
    nlinarith [(by norm_num : (1 : ℝ) * 2 ^ 170 ≤ 1 / 2 ^ 900 * 2 ^ 1075)]
  have hb0 := abs_nonneg b
  have he0 := abs_nonneg e
  -- `ch = xh yh`
  have hch := fapprox_mul (fapprox_self xh hxh) (fapprox_self yh hyh) |a| |c| le_rfl le_rfl P
    (by simp [hPdef]) (by linarith [(by norm_num : (2 : ℝ) ^ 899 < 2 ^ 1022)])
  have hche : |value (xh * yh).toBits - a * c| ≤ P / 2 ^ 53 + 1 / 2 ^ 1075 := by
    have h := hch.2
    simp only [zero_mul, mul_zero, add_zero, zero_add] at h
    exact h
  -- `cl1 = fma xh yh (-ch)`, the error of `ch`
  obtain ⟨hnf, hnv⟩ := TgammaFloor.neg_float _ hch.1
  have hS1 : |a * c - value (xh * yh).toBits| ≤ P / 2 ^ 52 := by
    rw [abs_sub_comm]
    have h170 : P / 2 ^ 170 ≤ P / 2 ^ 53 := div_le_div_of_nonneg_left hP0.le (by positivity)
      (by norm_num)
    have e : P / 2 ^ 53 + P / 2 ^ 53 = P / 2 ^ 52 := by ring
    linarith
  have hcl1 := fma_approx hF xh yh (-(xh * yh)) hxh hyh hnf (by
    rw [hnv, ← sub_eq_add_neg]
    linarith [div_le_self hP0.le (by norm_num : (1 : ℝ) ≤ 2 ^ 52)])
  rw [hnv, ← sub_eq_add_neg] at hcl1
  have hcl1e : |value (Fma.fma xh yh (-(xh * yh))).toBits - (a * c - value (xh * yh).toBits)| ≤
      P / 2 ^ 104 := by
    have h := hcl1.2
    have : |a * c - value (xh * yh).toBits| / 2 ^ 53 ≤ P / 2 ^ 52 / 2 ^ 53 :=
      div_le_div_of_nonneg_right hS1 (by norm_num)
    have e2 : P / 2 ^ 52 / 2 ^ 53 = P / 2 ^ 105 := by ring
    have : P / 2 ^ 170 ≤ P / 2 ^ 105 := div_le_div_of_nonneg_left hP0.le (by positivity)
      (by norm_num)
    have e3 : P / 2 ^ 105 + P / 2 ^ 105 = P / 2 ^ 104 := by ring
    linarith
  -- the cross terms
  have hxe : |a| * |e| ≤ P / 2 ^ 30 := by
    calc |a| * |e| ≤ |a| * (|c| / 2 ^ 30) := mul_le_mul_of_nonneg_left hylb (abs_nonneg _)
      _ = P / 2 ^ 30 := by rw [hPdef]; ring
  have hbc : |b| * |c| ≤ P / 2 ^ 30 := by
    calc |b| * |c| ≤ |a| / 2 ^ 30 * |c| := mul_le_mul_of_nonneg_right hxlb (abs_nonneg _)
      _ = P / 2 ^ 30 := by rw [hPdef]; ring
  have hbe : |b| * |e| ≤ P / 2 ^ 60 := by
    calc |b| * |e| ≤ |a| / 2 ^ 30 * (|c| / 2 ^ 30) := mul_le_mul hxlb hylb he0 (by positivity)
      _ = P / 2 ^ 60 := by rw [hPdef]; ring
  have hPm : P / 2 ^ 29 < 2 ^ 1022 := by
    have : P / 2 ^ 29 ≤ P := div_le_self hP0.le (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 899 < 2 ^ 1022)]
  have ht0 := fapprox_mul (fapprox_self xl hxl) (fapprox_self yl hyl) |b| |e| le_rfl le_rfl
    (P / 2 ^ 60) (by simp only [add_zero]; exact hbe) (by
      have : P / 2 ^ 60 ≤ P / 2 ^ 29 := div_le_div_of_nonneg_left hP0.le (by positivity)
        (by norm_num)
      linarith)
  have hm1 := fapprox_mul (fapprox_self xh hxh) (fapprox_self yl hyl) |a| |e| le_rfl le_rfl
    (P / 2 ^ 30) (by simp only [add_zero]; exact hxe) (by
      have : P / 2 ^ 30 ≤ P / 2 ^ 29 := div_le_div_of_nonneg_left hP0.le (by positivity)
        (by norm_num)
      linarith)
  have hm2 := fapprox_mul (fapprox_self xl hxl) (fapprox_self yh hyh) |b| |c| le_rfl le_rfl
    (P / 2 ^ 30) (by simp only [add_zero]; exact hbc) (by
      have : P / 2 ^ 30 ≤ P / 2 ^ 29 := div_le_div_of_nonneg_left hP0.le (by positivity)
        (by norm_num)
      linarith)
  simp only [zero_mul, mul_zero, add_zero, zero_add] at ht0 hm1 hm2
  -- `tl1 = xl yl + xh yl`
  have htl1 := fapprox_add ht0 hm1 (P * (1 / 2 ^ 29)) (by
      have h1 := abs_add_le (b * e) (a * e)
      rw [abs_mul, abs_mul] at h1
      have h2 : P / 2 ^ 60 / 2 ^ 53 + 1 / 2 ^ 1075 + (P / 2 ^ 30 / 2 ^ 53 + 1 / 2 ^ 1075) ≤
          P / 2 ^ 60 := by
        have e2 : P / 2 ^ 60 / 2 ^ 53 + P / 2 ^ 170 + (P / 2 ^ 30 / 2 ^ 53 + P / 2 ^ 170) =
            P * (1 / 2 ^ 113 + 2 / 2 ^ 170 + 1 / 2 ^ 83) := by ring
        have : P * (1 / 2 ^ 113 + 2 / 2 ^ 170 + 1 / 2 ^ 83) ≤ P * (1 / 2 ^ 60) :=
          mul_le_mul_of_nonneg_left (by norm_num) hP0.le
        have e3 : P * (1 / 2 ^ 60) = P / 2 ^ 60 := by ring
        linarith
      have e4 : P * (1 / 2 ^ 29) = P / 2 ^ 30 + P / 2 ^ 30 := by ring
      have : P / 2 ^ 60 + P / 2 ^ 60 ≤ P / 2 ^ 30 := by
        have e5 : P / 2 ^ 60 + P / 2 ^ 60 = P * (2 / 2 ^ 60) := by ring
        have e6 : P / 2 ^ 30 = P * (1 / 2 ^ 30) := by ring
        rw [e5, e6]; exact mul_le_mul_of_nonneg_left (by norm_num) hP0.le
      linarith) (by
      have : P * (1 / 2 ^ 29) ≤ P := by
        have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 29 ≤ 1) hP0.le
        linarith
      linarith [(by norm_num : (2 : ℝ) ^ 899 < 2 ^ 1023)])
  -- `cl2 = tl1 + xl yh`
  have hcl2 := fapprox_add htl1 hm2 (P * (1 / 2 ^ 28)) (by
      have h1 := abs_add_le (b * e + a * e) (b * c)
      have h1' := abs_add_le (b * e) (a * e)
      rw [abs_mul, abs_mul] at h1'
      rw [abs_mul] at h1
      have e2 : P / 2 ^ 60 / 2 ^ 53 + P / 2 ^ 170 + (P / 2 ^ 30 / 2 ^ 53 + P / 2 ^ 170) +
          P * (1 / 2 ^ 29) / 2 ^ 53 + (P / 2 ^ 30 / 2 ^ 53 + P / 2 ^ 170) + P / 2 ^ 60 +
          P / 2 ^ 30 + P / 2 ^ 30 ≤ P * (1 / 2 ^ 28) := by
        have e3 : P / 2 ^ 60 / 2 ^ 53 + P / 2 ^ 170 + (P / 2 ^ 30 / 2 ^ 53 + P / 2 ^ 170) +
            P * (1 / 2 ^ 29) / 2 ^ 53 + (P / 2 ^ 30 / 2 ^ 53 + P / 2 ^ 170) + P / 2 ^ 60 +
            P / 2 ^ 30 + P / 2 ^ 30 = P * (1 / 2 ^ 113 + 3 / 2 ^ 170 + 2 / 2 ^ 83 +
              1 / 2 ^ 82 + 1 / 2 ^ 60 + 2 / 2 ^ 30) := by ring
        rw [e3]; exact mul_le_mul_of_nonneg_left (by norm_num) hP0.le
      linarith) (by
      have : P * (1 / 2 ^ 28) ≤ P := by
        have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 28 ≤ 1) hP0.le
        linarith
      linarith [(by norm_num : (2 : ℝ) ^ 899 < 2 ^ 1023)])
  -- `cl3 = cl1 + cl2`
  have hcl3 := fapprox_add hcl1 hcl2 (P * (1 / 2 ^ 27)) (by
      have h1 := abs_add_le (a * c - value (xh * yh).toBits) (b * e + a * e + b * c)
      have h2 := abs_add_le (b * e + a * e) (b * c)
      have h3 := abs_add_le (b * e) (a * e)
      rw [abs_mul] at h2
      rw [abs_mul, abs_mul] at h3
      have e2 : P / 2 ^ 52 + (P / 2 ^ 60 + P / 2 ^ 30 + P / 2 ^ 30) +
          (|a * c - value (xh * yh).toBits| / 2 ^ 53 + 1 / 2 ^ 1075 +
            (P / 2 ^ 60 / 2 ^ 53 + 1 / 2 ^ 1075 + (P / 2 ^ 30 / 2 ^ 53 + 1 / 2 ^ 1075) +
              P * (1 / 2 ^ 29) / 2 ^ 53 + (P / 2 ^ 30 / 2 ^ 53 + 1 / 2 ^ 1075) +
              P * (1 / 2 ^ 28) / 2 ^ 53)) ≤ P * (1 / 2 ^ 27) := by
        have h4 : |a * c - value (xh * yh).toBits| / 2 ^ 53 ≤ P / 2 ^ 52 / 2 ^ 53 :=
          div_le_div_of_nonneg_right hS1 (by norm_num)
        have e3 : P / 2 ^ 52 + (P / 2 ^ 60 + P / 2 ^ 30 + P / 2 ^ 30) +
            (P / 2 ^ 52 / 2 ^ 53 + P / 2 ^ 170 +
              (P / 2 ^ 60 / 2 ^ 53 + P / 2 ^ 170 + (P / 2 ^ 30 / 2 ^ 53 + P / 2 ^ 170) +
                P * (1 / 2 ^ 29) / 2 ^ 53 + (P / 2 ^ 30 / 2 ^ 53 + P / 2 ^ 170) +
                P * (1 / 2 ^ 28) / 2 ^ 53)) =
            P * (1 / 2 ^ 52 + 1 / 2 ^ 60 + 2 / 2 ^ 30 + 1 / 2 ^ 105 + 4 / 2 ^ 170 +
              1 / 2 ^ 113 + 2 / 2 ^ 83 + 1 / 2 ^ 82 + 1 / 2 ^ 81) := by ring
        have : P * (1 / 2 ^ 52 + 1 / 2 ^ 60 + 2 / 2 ^ 30 + 1 / 2 ^ 105 + 4 / 2 ^ 170 +
            1 / 2 ^ 113 + 2 / 2 ^ 83 + 1 / 2 ^ 82 + 1 / 2 ^ 81) ≤ P * (1 / 2 ^ 27) :=
          mul_le_mul_of_nonneg_left (by norm_num) hP0.le
        linarith
      linarith) (by
      have : P * (1 / 2 ^ 27) ≤ P := by
        have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 27 ≤ 1) hP0.le
        linarith
      linarith [(by norm_num : (2 : ℝ) ^ 899 < 2 ^ 1023)])
  set cl3 := Fma.fma xh yh (-(xh * yh)) + (xl * yl + xh * yl + xl * yh) with hcl3d
  set ch := xh * yh with hchd
  have hE : |value cl3.toBits - (a * c - value ch.toBits + (b * e + a * e + b * c))| ≤
      P / 2 ^ 78 - P / 2 ^ 100 := by
    have h := hcl3.2
    have h4 : |a * c - value ch.toBits| / 2 ^ 53 ≤ P / 2 ^ 52 / 2 ^ 53 :=
      div_le_div_of_nonneg_right hS1 (by norm_num)
    have e3 : P / 2 ^ 52 / 2 ^ 53 + P / 2 ^ 170 +
        (P / 2 ^ 60 / 2 ^ 53 + P / 2 ^ 170 + (P / 2 ^ 30 / 2 ^ 53 + P / 2 ^ 170) +
          P * (1 / 2 ^ 29) / 2 ^ 53 + (P / 2 ^ 30 / 2 ^ 53 + P / 2 ^ 170) +
          P * (1 / 2 ^ 28) / 2 ^ 53) + P * (1 / 2 ^ 27) / 2 ^ 53 =
        P * (1 / 2 ^ 105 + 4 / 2 ^ 170 + 1 / 2 ^ 113 + 2 / 2 ^ 83 + 1 / 2 ^ 82 + 1 / 2 ^ 81 +
          1 / 2 ^ 80) := by ring
    have h5 : P * (1 / 2 ^ 105 + 4 / 2 ^ 170 + 1 / 2 ^ 113 + 2 / 2 ^ 83 + 1 / 2 ^ 82 +
        1 / 2 ^ 81 + 1 / 2 ^ 80) ≤ P * (1 / 2 ^ 78 - 1 / 2 ^ 100) :=
      mul_le_mul_of_nonneg_left (by norm_num) hP0.le
    have e4 : P * (1 / 2 ^ 78 - 1 / 2 ^ 100) = P / 2 ^ 78 - P / 2 ^ 100 := by ring
    linarith
  have hcl3b : |value cl3.toBits| ≤ P / 2 ^ 26 := by
    have h1 := abs_sub_abs_le_abs_sub (value cl3.toBits)
      (a * c - value ch.toBits + (b * e + a * e + b * c))
    have h2 := abs_add_le (a * c - value ch.toBits) (b * e + a * e + b * c)
    have h3 := abs_add_le (b * e + a * e) (b * c)
    have h4 := abs_add_le (b * e) (a * e)
    rw [abs_mul] at h3
    rw [abs_mul, abs_mul] at h4
    have e5 : P / 2 ^ 78 + P / 2 ^ 52 + (P / 2 ^ 60 + P / 2 ^ 30 + P / 2 ^ 30) ≤ P / 2 ^ 26 := by
      have e6 : P / 2 ^ 78 + P / 2 ^ 52 + (P / 2 ^ 60 + P / 2 ^ 30 + P / 2 ^ 30) =
          P * (1 / 2 ^ 78 + 1 / 2 ^ 52 + 1 / 2 ^ 60 + 2 / 2 ^ 30) := by ring
      have e7 : P / 2 ^ 26 = P * (1 / 2 ^ 26) := by ring
      rw [e6, e7]; exact mul_le_mul_of_nonneg_left (by norm_num) hP0.le
    have : 0 ≤ P / 2 ^ 100 := by positivity
    linarith
  have hchb1 : P - P / 2 ^ 52 ≤ |value ch.toBits| := by
    have := abs_sub_abs_le_abs_sub (a * c) (value ch.toBits)
    rw [abs_mul] at this
    linarith
  have hchb2 : |value ch.toBits| ≤ P + P / 2 ^ 52 := by
    have := abs_sub_abs_le_abs_sub (value ch.toBits) (a * c)
    rw [abs_mul] at this
    rw [abs_sub_comm] at hS1
    linarith
  have hord : |value cl3.toBits| ≤ |value ch.toBits| := by
    have : P / 2 ^ 26 + P / 2 ^ 52 ≤ P := by
      have e6 : P / 2 ^ 26 + P / 2 ^ 52 = P * (1 / 2 ^ 26 + 1 / 2 ^ 52) := by ring
      rw [e6]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 26 + 1 / 2 ^ 52 ≤ 1) hP0.le
      linarith
    linarith
  obtain ⟨hhf, hlf, hsum, hlt, hlb⟩ := fastTwoSum_spec ch cl3 hch.1 hcl3.1 hord
    (by linarith [(by norm_num : (2 : ℝ) ^ 899 + 2 ^ 899 / 2 ^ 52 < 2 ^ 900),
      div_le_div_of_nonneg_right hPmax (by norm_num : (0 : ℝ) ≤ 2 ^ 52)])
  have hmd : mulDD3 xh xl yh yl = fastTwoSum ch cl3 := rfl
  rw [hmd]
  have hhi1 : |value (fastTwoSum ch cl3).1.toBits| ≤ 2 * P := by
    have h1 := abs_sub_abs_le_abs_sub (value (fastTwoSum ch cl3).1.toBits)
      (-(value (fastTwoSum ch cl3).2.toBits))
    rw [sub_neg_eq_add, abs_neg, hsum] at h1
    have h2 := abs_add_le (value ch.toBits) (value cl3.toBits)
    have : P / 2 ^ 52 + 2 * (P / 2 ^ 26) ≤ P := by
      have e6 : P / 2 ^ 52 + 2 * (P / 2 ^ 26) = P * (1 / 2 ^ 52 + 2 / 2 ^ 26) := by ring
      rw [e6]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 52 + 2 / 2 ^ 26 ≤ 1) hP0.le
      linarith
    linarith
  have hhi2 : P / 2 ≤ |value (fastTwoSum ch cl3).1.toBits| := by
    have h1 := abs_sub_abs_le_abs_sub (value (fastTwoSum ch cl3).1.toBits +
      value (fastTwoSum ch cl3).2.toBits) (value (fastTwoSum ch cl3).2.toBits)
    rw [add_sub_cancel_right, hsum] at h1
    have h2 := abs_sub_abs_le_abs_sub (value ch.toBits) (-(value cl3.toBits))
    rw [sub_neg_eq_add, abs_neg] at h2
    have : P / 2 ^ 52 + 2 * (P / 2 ^ 26) ≤ P / 2 := by
      have e6 : P / 2 ^ 52 + 2 * (P / 2 ^ 26) = P * (1 / 2 ^ 52 + 2 / 2 ^ 26) := by ring
      have e7 : P / 2 = P * (1 / 2) := by ring
      rw [e6, e7]
      exact mul_le_mul_of_nonneg_left (by norm_num) hP0.le
    linarith
  refine ⟨hhf, hlf, ?_, ?_, hhi1, hhi2⟩
  · rw [hsum]
    have e : value ch.toBits + value cl3.toBits - (a + b) * (c + e) =
        value cl3.toBits - (a * c - value ch.toBits + (b * e + a * e + b * c)) := by ring
    rw [e]
    have : 0 ≤ P / 2 ^ 100 := by positivity
    linarith
  · refine hlb.trans ?_
    have : (1 : ℝ) / 2 ^ 1074 ≤ |value (fastTwoSum ch cl3).1.toBits| / 2 ^ 52 := by
      rw [le_div_iff₀ (by positivity)]
      have : P / 2 ≥ 1 / 2 ^ 901 := by linarith
      nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 * 2 ^ 52 ≤ 1 / 2 ^ 901)]
    have e6 : |value (fastTwoSum ch cl3).1.toBits| / 2 ^ 52 + |value (fastTwoSum ch cl3).1.toBits| /
        2 ^ 52 = |value (fastTwoSum ch cl3).1.toBits| / 2 ^ 51 := by ring
    linarith


#print axioms mulDD3_spec
#print axioms mulDD3_wide

end Verified.Examples.TgammaMulDD3
