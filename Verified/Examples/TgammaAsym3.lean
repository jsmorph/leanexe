import Verified.Examples.TgammaAsym1
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
The quantities of `Tgamma.asLgammaAsym` before its two branches, for `X = xh + xl` with
`4 ≤ xh ≤ 186`, `4 ≤ X ≤ 186`, and `|xl| ≤ 2 ^ -44`.  The rounded reciprocal `zh = 1/xh` lies
within `2 ^ -46 + 2 ^ -52` of `1/X` relative, since `xl` moves `1/X` by up to `2 ^ -46` relative,
and the corrected `zh + zl` lies within `2 ^ -78` (`asym_recip`).  The square `z2h + z2l` lies
within `2 ^ -76` of `1/X²` relative, and its high part `z2h`, the argument of the series, within
`2 ^ -44` (`asym_square`).  The first product lies within `2 ^ -61` of `(X - 1/2)(log X - 1)`
(`asym_front`): `asLogd` contributes `2 ^ -69 + |log xh| 2 ^ -78`, `dz = xl zh` replaces
`log X - log xh` within `2 ^ -90`, and the product of `TgammaAsym1.asym_prod` adds `2 ^ -63`.
-/

namespace Verified.Examples.TgammaAsym3
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaRecip TgammaRecipDD
  TgammaAsym1

set_option exponentiation.threshold 4096

theorem log_lo {x : ℝ} (h : 4 ≤ x) : 1386 / 1000 ≤ Real.log x := by
  have h2 := Real.log_two_gt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_le_log (by norm_num) h
  norm_num at h2
  linarith

theorem log_hi {x : ℝ} (h0 : 0 < x) (h : x ≤ 187) : Real.log x ≤ 529 / 100 := by
  rw [Real.log_le_iff_le_exp h0]
  have he := Real.exp_one_gt_d9
  have h1 : Real.exp (529 / 100) = Real.exp 1 ^ 5 * Real.exp (29 / 100) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  have h2 := Real.add_one_le_exp (29 / 100)
  have h3 : (148 : ℝ) ≤ Real.exp 1 ^ 5 := by
    have : (2.7182818283 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) he.le 5
    exact le_trans (by norm_num) this
  rw [h1]
  calc x ≤ 148 * (29 / 100 + 1) := by linarith
    _ ≤ Real.exp 1 ^ 5 * Real.exp (29 / 100) := mul_le_mul h3 h2 (by norm_num) (by positivity)

/-- **The reciprocal** `zh + zl` of `X = xh + xl`. -/
theorem asym_recip (hF : FmaSpec.FmaNearest) (xh xl : Float) (hxh : Finite xh.toBits)
    (hxl : Finite xl.toBits) (h4 : 4 ≤ value xh.toBits) (h186 : value xh.toBits ≤ 186)
    (hxlb : |value xl.toBits| ≤ 1 / 2 ^ 44) :
    Finite (1.0 / xh).toBits ∧
      Finite ((Fma.fma (1.0 / xh) (-xh) 1.0 - xl * (1.0 / xh)) * (1.0 / xh)).toBits ∧
      |value (1.0 / xh).toBits - 1 / value xh.toBits| ≤
        1 / value xh.toBits / 2 ^ 53 + 1 / 2 ^ 1075 ∧
      |value (1.0 / xh).toBits - 1 / (value xh.toBits + value xl.toBits)| ≤
        1 / (value xh.toBits + value xl.toBits) * (1 / 2 ^ 46 + 1 / 2 ^ 52) ∧
      |value (1.0 / xh).toBits +
          value ((Fma.fma (1.0 / xh) (-xh) 1.0 - xl * (1.0 / xh)) * (1.0 / xh)).toBits -
          1 / (value xh.toBits + value xl.toBits)| ≤
        1 / (value xh.toBits + value xl.toBits) / 2 ^ 78 ∧
      |value ((Fma.fma (1.0 / xh) (-xh) 1.0 - xl * (1.0 / xh)) * (1.0 / xh)).toBits| ≤
        1 / (value xh.toBits + value xl.toBits) / 2 ^ 44 := by
  have ha0 : 0 < value xh.toBits := by linarith
  have hk : |value xl.toBits| ≤ |value xh.toBits| / 2 ^ 40 := by
    rw [abs_of_pos ha0]
    exact hxlb.trans (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 44 ≤ 4 / 2 ^ 40)])
  obtain ⟨hzf, hlf, hsum, -, -⟩ := recip_dd hF xh xl hxh hxl hk
    (by rw [abs_of_pos ha0]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 600 ≤ 4)])
    (by rw [abs_of_pos ha0]; linarith [(by norm_num : (186 : ℝ) ≤ 2 ^ 600)])
  have hd := fapprox_div (fapprox_self _ one_finite) (fapprox_self xh hxh) 1 (value xh.toBits)
    (by simp [one_value]) (le_of_eq (abs_of_pos ha0).symm) ha0 (1 / value xh.toBits)
    (le_of_eq (by ring)) (by
      rw [div_lt_iff₀ ha0]
      linarith [(by norm_num : (1 : ℝ) ≤ 2 ^ 1022 * 4)])
  have hzd : |value (1.0 / xh).toBits - 1 / value xh.toBits| ≤
      1 / value xh.toBits / 2 ^ 53 + 1 / 2 ^ 1075 := by
    have h := hd.2
    rw [one_value] at h
    exact h.trans (le_of_eq (by ring))
  refine ⟨hzf, hlf, hzd, ?_⟩
  generalize value ((Fma.fma (1.0 / xh) (-xh) 1.0 - xl * (1.0 / xh)) * (1.0 / xh)).toBits = zl
    at hsum ⊢
  generalize value (1.0 / xh).toBits = zh at hsum hzd ⊢
  generalize value xl.toBits = e at hxlb hk hsum hzd ⊢
  generalize value xh.toBits = a at h4 h186 ha0 hk hsum hzd ⊢
  obtain ⟨he1, he2⟩ := abs_le.mp hxlb
  have hX0 : 0 < a + e := by linarith [(by norm_num : (1 : ℝ) / 2 ^ 44 ≤ 1)]
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 1 / (a + e) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = 1 / a := ⟨_, rfl⟩
  rw [← hZ] at hsum ⊢
  rw [← hR] at hzd
  have hZ0 : 0 < Z := by rw [hZ]; exact one_div_pos.mpr hX0
  have hR0 : 0 < R := by rw [hR]; exact one_div_pos.mpr ha0
  rw [abs_of_pos hZ0] at hsum
  have hZlo : 1 / 2 ^ 9 ≤ Z := by
    rw [hZ, div_le_div_iff₀ (by norm_num) hX0]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 44 ≤ 1)]
  have hR4 : R ≤ 1 / 4 := by
    rw [hR, div_le_div_iff₀ ha0 (by norm_num)]
    linarith
  have hZa : Z * (a + e) = 1 := by rw [hZ]; exact one_div_mul_cancel hX0.ne'
  have hRa : R * a = 1 := by rw [hR]; exact one_div_mul_cancel ha0.ne'
  have hRZ : R - Z = e * R * Z := by linear_combination (-R) * hZa + Z * hRa
  have h1 : |R - Z| ≤ Z / 2 ^ 46 := by
    rw [hRZ, abs_mul, abs_mul, abs_of_pos hR0, abs_of_pos hZ0]
    calc |e| * R * Z ≤ 1 / 2 ^ 44 * (1 / 4) * Z :=
          mul_le_mul (mul_le_mul hxlb hR4 hR0.le (by norm_num)) le_rfl hZ0.le (by positivity)
      _ = Z / 2 ^ 46 := by ring
  obtain ⟨h11, h12⟩ := abs_le.mp h1
  obtain ⟨h21, h22⟩ := abs_le.mp hzd
  have h3 : |zh - Z| ≤ Z * (1 / 2 ^ 46 + 1 / 2 ^ 52) := by
    rw [abs_le]
    constructor <;> linarith
  refine ⟨h3, hsum, ?_⟩
  obtain ⟨h31, h32⟩ := abs_le.mp h3
  obtain ⟨h51, h52⟩ := abs_le.mp hsum
  rw [abs_le]
  constructor <;> linarith

/-- **The square** `z2h + z2l` of `zh + zl ≈ Z`. -/
theorem asym_square (hF : FmaSpec.FmaNearest) (zh zl : Float) (hzh : Finite zh.toBits)
    (hzl : Finite zl.toBits) (Z : ℝ) (hZlo : 1 / 2 ^ 9 ≤ Z) (hZ : Z ≤ 1 / 2)
    (h1 : |value zh.toBits - Z| ≤ Z * (1 / 2 ^ 46 + 1 / 2 ^ 52))
    (h2 : |value zh.toBits + value zl.toBits - Z| ≤ Z / 2 ^ 78)
    (h3 : |value zl.toBits| ≤ Z / 2 ^ 44) :
    Finite (mulDD zh zl zh zl).1.toBits ∧ Finite (mulDD zh zl zh zl).2.toBits ∧
      |value (mulDD zh zl zh zl).1.toBits + value (mulDD zh zl zh zl).2.toBits - Z ^ 2| ≤
        Z ^ 2 / 2 ^ 76 ∧
      |value (mulDD zh zl zh zl).1.toBits - Z ^ 2| ≤ Z ^ 2 / 2 ^ 44 ∧
      |value (mulDD zh zl zh zl).2.toBits| ≤ Z ^ 2 / 2 ^ 42 := by
  have hZ0 : 0 < Z := lt_of_lt_of_le (by norm_num) hZlo
  have hZp : 0 ≤ Z * (1 + 1 / 2 ^ 45) := mul_nonneg hZ0.le (by norm_num)
  have hZl : 0 ≤ Z / 2 ^ 44 := div_nonneg hZ0.le (by norm_num)
  have hZZ : Z * Z ≤ 1 / 4 := by
    have := mul_le_mul hZ hZ hZ0.le (by norm_num)
    linarith
  have hZ2 : 1 / 2 ^ 18 ≤ Z ^ 2 := by
    have := mul_le_mul hZlo hZlo (by norm_num) hZ0.le
    linarith
  have hzhb : |value zh.toBits| ≤ Z * (1 + 1 / 2 ^ 45) := by
    have := abs_sub_abs_le_abs_sub (value zh.toBits) Z
    rw [abs_of_pos hZ0] at this
    linarith
  have hzh0 := abs_nonneg (value zh.toBits)
  have hzl0 := abs_nonneg (value zl.toBits)
  obtain ⟨hf1, hf2, he, hlow, -⟩ := mulDD_spec hF zh zl zh zl hzh hzl hzh hzl
    (Z * (1 + 1 / 2 ^ 45) * (Z * (1 + 1 / 2 ^ 45))) (Z * (1 + 1 / 2 ^ 45) * (Z / 2 ^ 44))
    (Z / 2 ^ 44 * (Z * (1 + 1 / 2 ^ 45))) (Z / 2 ^ 44 * (Z / 2 ^ 44))
    (mul_le_mul hzhb hzhb hzh0 hZp) (mul_le_mul hzhb h3 hzl0 hZp)
    (mul_le_mul h3 hzhb hzh0 hZl) (mul_le_mul h3 h3 hzl0 hZl)
    (by linarith) (by linarith)
  have hT1 : (1 : ℝ) / 2 ^ 1070 ≤ Z ^ 2 / 2 ^ 1000 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    linarith
  -- the exact square of `zh + zl`
  have hsq : |(value zh.toBits + value zl.toBits) * (value zh.toBits + value zl.toBits) - Z ^ 2| ≤
      Z / 2 ^ 78 * (Z * (2 + 1 / 2 ^ 78)) := by
    rw [show (value zh.toBits + value zl.toBits) * (value zh.toBits + value zl.toBits) - Z ^ 2 =
      (value zh.toBits + value zl.toBits - Z) * (value zh.toBits + value zl.toBits - Z + 2 * Z) by
        ring, abs_mul]
    have : |value zh.toBits + value zl.toBits - Z + 2 * Z| ≤ Z * (2 + 1 / 2 ^ 78) := by
      have := abs_add_le (value zh.toBits + value zl.toBits - Z) (2 * Z)
      rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * Z)] at this
      linarith
    exact mul_le_mul h2 this (abs_nonneg _) (div_nonneg hZ0.le (by norm_num))
  -- the rounded high part `zh * zh`
  have hzz : |value zh.toBits| * |value zh.toBits| ≤ Z * (1 + 1 / 2 ^ 45) * (Z * (1 + 1 / 2 ^ 45)) :=
    mul_le_mul hzhb hzhb hzh0 hZp
  have hm := fapprox_mul (fapprox_self zh hzh) (fapprox_self zh hzh) |value zh.toBits|
    |value zh.toBits| le_rfl le_rfl (|value zh.toBits| * |value zh.toBits|) (le_of_eq (by ring))
    (by linarith)
  have hm2 : |value (zh * zh).toBits - value zh.toBits * value zh.toBits| ≤
      |value zh.toBits| * |value zh.toBits| / 2 ^ 53 + 1 / 2 ^ 1075 := by
    have := hm.2
    simp only [zero_mul, mul_zero, zero_add, add_zero] at this
    exact this
  have hsq1 : |value zh.toBits * value zh.toBits - Z ^ 2| ≤
      Z * (1 / 2 ^ 46 + 1 / 2 ^ 52) * (Z * (2 + 1 / 2 ^ 45)) := by
    rw [show value zh.toBits * value zh.toBits - Z ^ 2 =
      (value zh.toBits - Z) * (value zh.toBits - Z + 2 * Z) by ring, abs_mul]
    have : |value zh.toBits - Z + 2 * Z| ≤ Z * (2 + 1 / 2 ^ 45) := by
      have := abs_add_le (value zh.toBits - Z) (2 * Z)
      rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * Z)] at this
      linarith
    exact mul_le_mul h1 this (abs_nonneg _) (mul_nonneg hZ0.le (by norm_num))
  have hh : (mulDD zh zl zh zl).1 = zh * zh := rfl
  refine ⟨hf1, hf2, ?_, ?_, ?_⟩
  · have := abs_add_le (value (mulDD zh zl zh zl).1.toBits + value (mulDD zh zl zh zl).2.toBits -
      (value zh.toBits + value zl.toBits) * (value zh.toBits + value zl.toBits))
      ((value zh.toBits + value zl.toBits) * (value zh.toBits + value zl.toBits) - Z ^ 2)
    rw [sub_add_sub_cancel] at this
    linarith
  · rw [hh]
    have := abs_add_le (value (zh * zh).toBits - value zh.toBits * value zh.toBits)
      (value zh.toBits * value zh.toBits - Z ^ 2)
    rw [sub_add_sub_cancel] at this
    have : (1 : ℝ) / 2 ^ 1075 ≤ Z ^ 2 / 2 ^ 1000 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      linarith
    linarith
  · linarith

/-- `|log (1 + t) - t| ≤ 2 ^ -91` for `|t| ≤ 2 ^ -46`. -/
theorem log_one_add (t : ℝ) (ht : |t| ≤ 1 / 2 ^ 46) : |Real.log (1 + t) - t| ≤ 1 / 2 ^ 91 := by
  have ht1 : |-t| < 1 := by rw [abs_neg]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 46 < 1)]
  have h := Real.abs_log_sub_add_sum_range_le ht1 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one, sub_neg_eq_add,
    abs_neg, Nat.reduceAdd] at h
  rw [show Real.log (1 + t) - t = -t + Real.log (1 + t) by ring]
  refine h.trans ?_
  have h0 : 0 ≤ |t| := abs_nonneg t
  rw [div_le_iff₀ (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 46 < 1)])]
  have : |t| ^ 2 ≤ (1 / 2 ^ 46) ^ 2 := pow_le_pow_left₀ h0 ht 2
  linarith

/-- **The first product** of `asLgammaAsym` within `2 ^ -61` of `(X - 1/2)(log X - 1)`. -/
theorem asym_front (hF : FmaSpec.FmaNearest) (xh xl lh ll : Float) (hxh : Finite xh.toBits)
    (hxl : Finite xl.toBits) (hlh : Finite lh.toBits) (hll : Finite ll.toBits)
    (h4 : 4 ≤ value xh.toBits) (h186 : value xh.toBits ≤ 186)
    (hX4 : 4 ≤ value xh.toBits + value xl.toBits) (hX186 : value xh.toBits + value xl.toBits ≤ 186)
    (hxlb : |value xl.toBits| ≤ 1 / 2 ^ 44)
    (hle : |value lh.toBits + value ll.toBits - Real.log (value xh.toBits)| ≤
      1 / 2 ^ 69 + |Real.log (value xh.toBits)| / 2 ^ 78)
    (hllb : |value ll.toBits| ≤ 1 / 2 ^ 22 + |value lh.toBits| / 2 ^ 52) :
    Finite (mulDD (xh - 0.5) xl (lh - 1.0) (ll + xl * (1.0 / xh))).1.toBits ∧
      Finite (mulDD (xh - 0.5) xl (lh - 1.0) (ll + xl * (1.0 / xh))).2.toBits ∧
      |value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + xl * (1.0 / xh))).1.toBits +
          value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + xl * (1.0 / xh))).2.toBits -
          (value xh.toBits + value xl.toBits - 1 / 2) *
            (Real.log (value xh.toBits + value xl.toBits) - 1)| ≤ 1 / 2 ^ 61 ∧
      |value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + xl * (1.0 / xh))).2.toBits| ≤ 73 / 100 / 2 ^ 14 ∧
      1 ≤ value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + xl * (1.0 / xh))).1.toBits ∧
      value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + xl * (1.0 / xh))).1.toBits ≤ 797 := by
  have ha0 : 0 < value xh.toBits := by linarith
  have hla1 := log_lo h4
  have hla2 := log_hi (x := value xh.toBits) ha0 (by linarith)
  have hlX1 := log_lo hX4
  have hlX2 := log_hi (x := value xh.toBits + value xl.toBits) (by linarith) (by linarith)
  rw [abs_of_pos (by linarith : 0 < Real.log (value xh.toBits))] at hle
  obtain ⟨hle1, hle2⟩ := abs_le.mp hle
  obtain ⟨he1, he2⟩ := abs_le.mp hxlb
  -- the high part of the logarithm
  have hlh1 : 13 / 10 ≤ value lh.toBits ∧ value lh.toBits ≤ 53 / 10 := by
    rcases le_or_gt 0 (value lh.toBits) with hp | hn
    · rw [abs_of_nonneg hp] at hllb
      obtain ⟨hl1, hl2⟩ := abs_le.mp hllb
      constructor <;> linarith
    · rw [abs_of_neg hn] at hllb
      obtain ⟨hl1, hl2⟩ := abs_le.mp hllb
      exfalso
      linarith
  -- the reciprocal and `dz = xl zh`
  obtain ⟨hzf, -, hzd, hzX, -, -⟩ := asym_recip hF xh xl hxh hxl h4 h186 hxlb
  have hX0 : 0 < value xh.toBits + value xl.toBits := by linarith
  have hZ4 : 1 / (value xh.toBits + value xl.toBits) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hX0 (by norm_num)]
    linarith
  have hZ0 : 0 < 1 / (value xh.toBits + value xl.toBits) := one_div_pos.mpr hX0
  have hzb : |value (1.0 / xh).toBits| ≤ 1 / 4 + 1 / 2 ^ 40 := by
    have := abs_sub_abs_le_abs_sub (value (1.0 / xh).toBits) (1 / (value xh.toBits + value xl.toBits))
    rw [abs_of_pos hZ0] at this
    linarith
  have hez : |value xl.toBits| * |value (1.0 / xh).toBits| ≤ 1 / 2 ^ 44 * (1 / 4 + 1 / 2 ^ 40) :=
    mul_le_mul hxlb hzb (abs_nonneg _) (by norm_num)
  have hm := fapprox_mul (fapprox_self xl hxl) (fapprox_self _ hzf) |value xl.toBits|
    |value (1.0 / xh).toBits| le_rfl le_rfl (|value xl.toBits| * |value (1.0 / xh).toBits|)
    (le_of_eq (by ring)) (by linarith)
  have hm2 : |value (xl * (1.0 / xh)).toBits - value xl.toBits * value (1.0 / xh).toBits| ≤
      |value xl.toBits| * |value (1.0 / xh).toBits| / 2 ^ 53 + 1 / 2 ^ 1075 := by
    have := hm.2
    simp only [zero_mul, mul_zero, zero_add, add_zero] at this
    exact this
  have hdzb : |value (xl * (1.0 / xh)).toBits| ≤ 1 / 2 ^ 45 := by
    have := abs_sub_abs_le_abs_sub (value (xl * (1.0 / xh)).toBits)
      (value xl.toBits * value (1.0 / xh).toBits)
    rw [abs_mul] at this
    linarith
  have hR4 : 1 / value xh.toBits ≤ 1 / 4 := by
    rw [div_le_div_iff₀ ha0 (by norm_num)]
    linarith
  have hdz : |value (xl * (1.0 / xh)).toBits - value xl.toBits / value xh.toBits| ≤ 1 / 2 ^ 96 := by
    have h1 : |value xl.toBits * value (1.0 / xh).toBits - value xl.toBits / value xh.toBits| ≤
        1 / 2 ^ 44 * (1 / 4 / 2 ^ 53 + 1 / 2 ^ 1075) := by
      rw [show value xl.toBits * value (1.0 / xh).toBits - value xl.toBits / value xh.toBits =
        value xl.toBits * (value (1.0 / xh).toBits - 1 / value xh.toBits) by ring, abs_mul]
      refine mul_le_mul hxlb (hzd.trans ?_) (abs_nonneg _) (by norm_num)
      linarith [div_le_div_of_nonneg_right hR4 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)]
    have := abs_add_le (value (xl * (1.0 / xh)).toBits - value xl.toBits * value (1.0 / xh).toBits)
      (value xl.toBits * value (1.0 / xh).toBits - value xl.toBits / value xh.toBits)
    rw [sub_add_sub_cancel] at this
    linarith
  -- `log X = log xh + log (1 + xl/xh)`
  have ht : |value xl.toBits / value xh.toBits| ≤ 1 / 2 ^ 46 := by
    rw [abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
    linarith
  have hlog := log_one_add _ ht
  have hX : value xh.toBits + value xl.toBits =
      value xh.toBits * (1 + value xl.toBits / value xh.toBits) := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ ha0.ne']
  have hlogX : Real.log (value xh.toBits + value xl.toBits) =
      Real.log (value xh.toBits) + Real.log (1 + value xl.toBits / value xh.toBits) := by
    rw [hX, Real.log_mul ha0.ne' (ne_of_gt (by
      linarith [(abs_le.mp ht).1, (by norm_num : (1 : ℝ) / 2 ^ 46 < 1)]))]
  -- the product
  obtain ⟨hpf1, hpf2, hpe, hplow, -⟩ := asym_prod hF xh xl lh ll (xl * (1.0 / xh)) hxh hxl hlh hll
    hm.1 h4 h186 hxlb hlh1.1 hlh1.2 hllb hdzb
  have hD : |value lh.toBits + value ll.toBits + value (xl * (1.0 / xh)).toBits -
      Real.log (value xh.toBits + value xl.toBits)| ≤
      1 / 2 ^ 69 + 529 / 100 / 2 ^ 78 + 1 / 2 ^ 96 + 1 / 2 ^ 91 := by
    rw [hlogX]
    obtain ⟨h11, h12⟩ := abs_le.mp hdz
    obtain ⟨h21, h22⟩ := abs_le.mp hlog
    rw [abs_le]
    constructor <;> linarith
  have hXh : |value xh.toBits + value xl.toBits - 1 / 2| ≤ 371 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hprod : |(value xh.toBits - 1 / 2 + value xl.toBits) *
      (value lh.toBits + value ll.toBits + value (xl * (1.0 / xh)).toBits - 1) -
      (value xh.toBits + value xl.toBits - 1 / 2) *
        (Real.log (value xh.toBits + value xl.toBits) - 1)| ≤
      371 / 2 * (1 / 2 ^ 69 + 529 / 100 / 2 ^ 78 + 1 / 2 ^ 96 + 1 / 2 ^ 91) := by
    rw [show (value xh.toBits - 1 / 2 + value xl.toBits) *
        (value lh.toBits + value ll.toBits + value (xl * (1.0 / xh)).toBits - 1) -
        (value xh.toBits + value xl.toBits - 1 / 2) *
          (Real.log (value xh.toBits + value xl.toBits) - 1) =
        (value xh.toBits + value xl.toBits - 1 / 2) *
          (value lh.toBits + value ll.toBits + value (xl * (1.0 / xh)).toBits -
            Real.log (value xh.toBits + value xl.toBits)) by ring, abs_mul]
    exact mul_le_mul hXh hD (abs_nonneg _) (by norm_num)
  have hE : |value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + xl * (1.0 / xh))).1.toBits +
      value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + xl * (1.0 / xh))).2.toBits -
      (value xh.toBits + value xl.toBits - 1 / 2) *
        (Real.log (value xh.toBits + value xl.toBits) - 1)| ≤ 1 / 2 ^ 61 := by
    have := abs_add_le (value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + xl * (1.0 / xh))).1.toBits +
      value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + xl * (1.0 / xh))).2.toBits -
      (value xh.toBits - 1 / 2 + value xl.toBits) *
        (value lh.toBits + value ll.toBits + value (xl * (1.0 / xh)).toBits - 1))
      ((value xh.toBits - 1 / 2 + value xl.toBits) *
        (value lh.toBits + value ll.toBits + value (xl * (1.0 / xh)).toBits - 1) -
        (value xh.toBits + value xl.toBits - 1 / 2) *
          (Real.log (value xh.toBits + value xl.toBits) - 1))
    rw [sub_add_sub_cancel] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 63 +
      371 / 2 * (1 / 2 ^ 69 + 529 / 100 / 2 ^ 78 + 1 / 2 ^ 96 + 1 / 2 ^ 91) ≤ 1 / 2 ^ 61)]
  refine ⟨hpf1, hpf2, hE, hplow, ?_⟩
  -- the bounds of `(X - 1/2)(log X - 1)`
  have hV1 : 7 / 2 * (386 / 1000) ≤ (value xh.toBits + value xl.toBits - 1 / 2) *
      (Real.log (value xh.toBits + value xl.toBits) - 1) :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have hV2 : (value xh.toBits + value xl.toBits - 1 / 2) *
      (Real.log (value xh.toBits + value xl.toBits) - 1) ≤ 371 / 2 * (429 / 100) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  obtain ⟨h1, h2⟩ := abs_le.mp hE
  obtain ⟨h3, h4⟩ := abs_le.mp hplow
  constructor <;> linarith [(by norm_num : (1 : ℝ) / 2 ^ 61 ≤ 1 / 100),
    (by norm_num : (73 : ℝ) / 100 / 2 ^ 14 ≤ 1 / 100)]

#print axioms asym_recip
#print axioms asym_square
#print axioms asym_front

end Verified.Examples.TgammaAsym3
