import Library.Numerics.Float64.Lgamma.LgammaRecip

/-!
The double-double reciprocal of `Lgamma.asLgammaAsymAccurate`: `zh = 1/xh` and
`zl = (fma (zh, -xh, 1) - xl zh) zh` approximate `1/(xh + xl)` within `2^-98/xh` for
`1 ≤ xh ≤ 2^120` and `|xl| ≤ xh/2^51` (`recip_dd`).  With `R = 1/xh`, `S = 1 - zh xh`, and
`a = xl R`, `zh = R (1 - S)` and
`zh + S zh - xl zh² - 1/(xh + xl) = R (-S² + a (2 S - S²) - a²/(1 + a))`, at most about
`2^-100.2 R` since `|S| ≤ 2^-52` and `|a| ≤ 2^-51`.  The roundings of the `fma`, of `xl zh`, of the
difference, and of the product add about `2^-101.4 R`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAsymRecip
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaRecip

set_option exponentiation.threshold 4096

set_option maxHeartbeats 1000000 in
/-- **The double-double reciprocal** `zh + zl ≈ 1/(xh + xl)`. -/
theorem recip_dd (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (xh xl : Float) (hxh : Finite xh.toBits)
    (hxl : Finite xl.toBits) (hlo : 1 ≤ value xh.toBits) (hhi : value xh.toBits ≤ 2 ^ 120)
    (hlb : |value xl.toBits| ≤ value xh.toBits / 2 ^ 51) :
    Finite (1.0 / xh).toBits ∧
      Finite ((Library.Numerics.Arithmetic.Fma.fma (1.0 / xh) (-xh) 1.0 - xl * (1.0 / xh)) * (1.0 / xh)).toBits ∧
      |value (1.0 / xh).toBits - 1 / value xh.toBits| ≤ 1 / value xh.toBits / 2 ^ 52 ∧
      |value ((Library.Numerics.Arithmetic.Fma.fma (1.0 / xh) (-xh) 1.0 - xl * (1.0 / xh)) * (1.0 / xh)).toBits| ≤
        1 / value xh.toBits / 2 ^ 49 ∧
      |value (1.0 / xh).toBits +
          value ((Library.Numerics.Arithmetic.Fma.fma (1.0 / xh) (-xh) 1.0 - xl * (1.0 / xh)) * (1.0 / xh)).toBits -
          1 / (value xh.toBits + value xl.toBits)| ≤ 1 / value xh.toBits / 2 ^ 98 := by
  set vx := value xh.toBits with hvx
  set vl := value xl.toBits with hvl
  have hx0 : 0 < vx := by linarith
  set R := 1 / vx with hRdef
  have hR0 : 0 < R := by positivity
  have hRvx : R * vx = 1 := by rw [hRdef]; field_simp
  have hR1 : R ≤ 1 := by rw [hRdef, div_le_one hx0]; exact hlo
  have hRlo : 1 / 2 ^ 120 ≤ R := by
    rw [hRdef, div_le_div_iff₀ (by positivity) hx0]; linarith
  obtain ⟨hzf, -, hz1, -, -⟩ := LgammaRecip.recip_wide hF xh hxh
    (by rw [abs_of_pos hx0]; exact hlo)
    (by rw [abs_of_pos hx0]; linarith [(by norm_num : (2 : ℝ) ^ 120 ≤ 2 ^ 170)])
  rw [abs_of_pos (show (0 : ℝ) < 1 / vx by positivity)] at hz1
  set zh := 1.0 / xh with hzhdef
  set z := value zh.toBits with hzdef
  have hze : |z - R| ≤ R / 2 ^ 52 := hz1
  have hzb : |z| ≤ R * (1 + 1 / 2 ^ 52) := by
    have := abs_sub_abs_le_abs_sub z R
    rw [abs_of_pos hR0] at this
    linarith
  -- the residual `S = 1 - z vx` and `z = R (1 - S)`
  have hnx := fapprox_neg (fapprox_self xh hxh)
  have hnxv : value (-xh).toBits = -vx := by
    have h0 := abs_nonpos_iff.mp hnx.2
    linarith
  set S := z * value (-xh).toBits + value (1.0 : Float).toBits with hS
  have hSv : S = 1 - z * vx := by rw [hS, hnxv, one_value]; ring
  have hzS : z = R * (1 - S) := by
    rw [hSv, hRdef]; field_simp; ring
  have hSb : |S| ≤ 1 / 2 ^ 52 := by
    have h1 : S = -vx * (z - R) := by
      rw [hSv, hRdef]; field_simp; ring
    rw [h1, abs_mul, abs_neg, abs_of_pos hx0]
    calc vx * |z - R| ≤ vx * (R / 2 ^ 52) := mul_le_mul_of_nonneg_left hze hx0.le
      _ = 1 / 2 ^ 52 := by rw [mul_div_assoc', mul_comm vx R, hRvx]
  have hr := fma_approx hF zh (-xh) 1.0 hzf hnx.1 one_finite
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 2 ^ 1000)])
  rw [← hS] at hr
  set r := Library.Numerics.Arithmetic.Fma.fma zh (-xh) 1.0 with hrdef
  have hre : |value r.toBits - S| ≤ 1 / 2 ^ 105 + 1 / 2 ^ 1075 := by
    have := hr.2
    have : |S| / 2 ^ 53 ≤ 1 / 2 ^ 105 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hrA : FApprox r S (1 / 2 ^ 105 + 1 / 2 ^ 1075) := ⟨hr.1, hre⟩
  -- `dz = xl zh`
  have hvlb : |vl| ≤ vx / 2 ^ 51 := hlb
  have hdz := fapprox_mul (fapprox_self xl hxl) (fapprox_self zh hzf) (vx / 2 ^ 51)
    (R * (1 + 1 / 2 ^ 52)) hvlb hzb (1 / 2 ^ 51 * (1 + 1 / 2 ^ 52)) (by
      simp only [add_zero]
      rw [show vx / 2 ^ 51 * (R * (1 + 1 / 2 ^ 52)) = R * vx / 2 ^ 51 * (1 + 1 / 2 ^ 52) by ring,
        hRvx])
    (by norm_num)
  simp only [mul_zero, zero_mul, add_zero, zero_add] at hdz
  set dz := xl * zh with hdzdef
  -- `t = r - dz`
  have hvlz : |vl * z| ≤ 1 / 2 ^ 51 * (1 + 1 / 2 ^ 52) := by
    rw [abs_mul]
    calc |vl| * |z| ≤ vx / 2 ^ 51 * (R * (1 + 1 / 2 ^ 52)) :=
          mul_le_mul hvlb hzb (abs_nonneg _) (by positivity)
      _ = R * vx / 2 ^ 51 * (1 + 1 / 2 ^ 52) := by ring
      _ = 1 / 2 ^ 51 * (1 + 1 / 2 ^ 52) := by rw [hRvx]
  have hSz : |S - vl * z| ≤ 1 / 2 ^ 50 * (4 / 5) := by
    have := abs_sub S (vl * z)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 + 1 / 2 ^ 51 * (1 + 1 / 2 ^ 52) ≤
      1 / 2 ^ 50 * (4 / 5))]
  have ht := fapprox_sub hrA hdz (1 / 2 ^ 50) (by
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 * (4 / 5) + (1 / 2 ^ 105 + 1 / 2 ^ 1075 +
        (1 / 2 ^ 51 * (1 + 1 / 2 ^ 52) / 2 ^ 53 + 1 / 2 ^ 1075)) ≤ 1 / 2 ^ 50)])
    (by norm_num)
  set t := r - dz with htdef
  set et : ℝ := 1 / 2 ^ 105 + 1 / 2 ^ 1075 + (1 / 2 ^ 51 * (1 + 1 / 2 ^ 52) / 2 ^ 53 + 1 / 2 ^ 1075) +
    1 / 2 ^ 50 / 2 ^ 53 with hetdef
  have het : et ≤ 1 / 2 ^ 102 := by rw [hetdef]; norm_num
  -- `zl = t zh`
  have hzl := fapprox_mul ht (fapprox_self zh hzf) (1 / 2 ^ 50 * (4 / 5)) (R * (1 + 1 / 2 ^ 52))
    hSz hzb ((1 / 2 ^ 50 * (4 / 5) + et) * (R * (1 + 1 / 2 ^ 52) + 0)) le_rfl (by
      have h1 : 1 / 2 ^ 50 * (4 / 5) + et ≤ 1 / 2 := by
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 * (4 / 5) + 1 / 2 ^ 102 ≤ 1 / 2)]
      have h2 : R * (1 + 1 / 2 ^ 52) + 0 ≤ 2 := by nlinarith
      have h3 := mul_le_mul h1 h2 (by nlinarith) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      linarith [(by norm_num : (1 : ℝ) / 2 * 2 < 2 ^ 1022)])
  simp only [mul_zero, add_zero] at hzl
  set zl := t * zh with hzldef
  -- the error of `zl` against `(S - vl z) z`
  have hzle : |value zl.toBits - (S - vl * z) * z| ≤ R / 2 ^ 101 := by
    have h := hzl.2
    have e1 : et * (R * (1 + 1 / 2 ^ 52)) ≤ R / 2 ^ 102 * (1 + 1 / 2 ^ 52) := by
      have := mul_le_mul_of_nonneg_right het (mul_nonneg hR0.le (by norm_num) : (0 : ℝ) ≤ R * (1 + 1 / 2 ^ 52))
      linarith
    have e2 : (1 / 2 ^ 50 * (4 / 5) + et) * (R * (1 + 1 / 2 ^ 52)) / 2 ^ 53 ≤
        R / 2 ^ 103 * (1 + 1 / 2 ^ 52) := by
      have h1 : 1 / 2 ^ 50 * (4 / 5) + et ≤ 1 / 2 ^ 50 := by
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 * (4 / 5) + 1 / 2 ^ 102 ≤ 1 / 2 ^ 50)]
      have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hR0.le (by norm_num) : (0 : ℝ) ≤ R * (1 + 1 / 2 ^ 52))
      have h2 := div_le_div_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 2 ^ 53)
      linarith [(by ring : 1 / 2 ^ 50 * (R * (1 + 1 / 2 ^ 52)) / 2 ^ 53 =
        R / 2 ^ 103 * (1 + 1 / 2 ^ 52))]
    have e3 : (1 : ℝ) / 2 ^ 1075 ≤ R / 2 ^ 900 := by
      have := div_le_div_of_nonneg_right hRlo (by positivity : (0 : ℝ) ≤ 2 ^ 900)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 120 / 2 ^ 900)]
    have e4 : R / 2 ^ 102 * (1 + 1 / 2 ^ 52) + R / 2 ^ 103 * (1 + 1 / 2 ^ 52) + R / 2 ^ 900 ≤
        R / 2 ^ 101 := by
      have : R / 2 ^ 102 * (1 + 1 / 2 ^ 52) + R / 2 ^ 103 * (1 + 1 / 2 ^ 52) + R / 2 ^ 900 =
          R * (1 / 2 ^ 102 * (1 + 1 / 2 ^ 52) + 1 / 2 ^ 103 * (1 + 1 / 2 ^ 52) + 1 / 2 ^ 900) := by
        ring
      rw [this]
      have h5 : (1 : ℝ) / 2 ^ 102 * (1 + 1 / 2 ^ 52) + 1 / 2 ^ 103 * (1 + 1 / 2 ^ 52) +
          1 / 2 ^ 900 ≤ 1 / 2 ^ 101 := by norm_num
      have := mul_le_mul_of_nonneg_left h5 hR0.le
      linarith
    linarith
  -- the mathematics: `z + (S - vl z) z - 1/(vx + vl)`
  set a := vl * R with hadef
  have ha : |a| ≤ 1 / 2 ^ 51 := by
    rw [hadef, abs_mul, abs_of_pos hR0]
    calc |vl| * R ≤ vx / 2 ^ 51 * R := mul_le_mul_of_nonneg_right hvlb hR0.le
      _ = R * vx / 2 ^ 51 := by ring
      _ = 1 / 2 ^ 51 := by rw [hRvx]
  have ha1 : 1 / 2 ≤ 1 + a := by
    have := (abs_le.mp ha).1
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 51 ≤ 1 / 2)]
  have hX : vx + vl = vx * (1 + a) := by
    rw [hadef, hRdef]; field_simp
  have hX0 : 0 < vx + vl := by rw [hX]; nlinarith
  have hid : z + (S - vl * z) * z - 1 / (vx + vl) =
      R * (-(S ^ 2) + a * (2 * S - S ^ 2) - a ^ 2 / (1 + a)) := by
    have hvx0 : vx ≠ 0 := hx0.ne'
    rw [hzS, hX, hadef, hRdef]
    have h1 : (1 : ℝ) + vl * (1 / vx) ≠ 0 := by
      have : (0 : ℝ) < 1 + vl * (1 / vx) := by
        have := ha1
        rw [hadef, hRdef] at this
        linarith
      exact this.ne'
    field_simp
    ring
  have hmath : |z + (S - vl * z) * z - 1 / (vx + vl)| ≤ R / 2 ^ 100 := by
    rw [hid, abs_mul, abs_of_pos hR0]
    have hS2 : S ^ 2 ≤ 1 / 2 ^ 104 := by
      have := pow_le_pow_left₀ (abs_nonneg S) hSb 2
      rw [sq_abs] at this
      linarith [(by norm_num : ((1 : ℝ) / 2 ^ 52) ^ 2 = 1 / 2 ^ 104)]
    have hS0 : 0 ≤ S ^ 2 := sq_nonneg S
    have ha2 : a ^ 2 ≤ 1 / 2 ^ 102 := by
      have := pow_le_pow_left₀ (abs_nonneg a) ha 2
      rw [sq_abs] at this
      linarith [(by norm_num : ((1 : ℝ) / 2 ^ 51) ^ 2 = 1 / 2 ^ 102)]
    have hq : |a ^ 2 / (1 + a)| ≤ 1 / 2 ^ 101 := by
      rw [abs_div, abs_of_nonneg (sq_nonneg a), abs_of_pos (by linarith : (0 : ℝ) < 1 + a),
        div_le_iff₀ (by linarith)]
      nlinarith
    have hb : |a * (2 * S - S ^ 2)| ≤ 1 / 2 ^ 51 * (2 / 2 ^ 52 + 1 / 2 ^ 104) := by
      rw [abs_mul]
      apply mul_le_mul ha _ (abs_nonneg _) (by norm_num)
      have := abs_sub (2 * S) (S ^ 2)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hS0] at this
      linarith
    have h1 := abs_add_le (-(S ^ 2) + a * (2 * S - S ^ 2)) (-(a ^ 2 / (1 + a)))
    have h2 := abs_add_le (-(S ^ 2)) (a * (2 * S - S ^ 2))
    rw [abs_neg, abs_of_nonneg hS0] at h2
    rw [abs_neg, ← sub_eq_add_neg] at h1
    have h3 : |-(S ^ 2) + a * (2 * S - S ^ 2) - a ^ 2 / (1 + a)| ≤ 1 / 2 ^ 100 := by
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 104 + 1 / 2 ^ 51 * (2 / 2 ^ 52 + 1 / 2 ^ 104) +
        1 / 2 ^ 101 ≤ 1 / 2 ^ 100)]
    have := mul_le_mul_of_nonneg_left h3 hR0.le
    linarith [(by ring : R * (1 / 2 ^ 100) = R / 2 ^ 100)]
  refine ⟨hzf, hzl.1, hze, ?_, ?_⟩
  · -- `|zl| ≤ R/2^49`
    have h1 := abs_sub_abs_le_abs_sub (value zl.toBits) ((S - vl * z) * z)
    have h2 : |(S - vl * z) * z| ≤ 1 / 2 ^ 50 * (4 / 5) * (R * (1 + 1 / 2 ^ 52)) := by
      rw [abs_mul]; exact mul_le_mul hSz hzb (abs_nonneg _) (by norm_num)
    have h3 : 1 / 2 ^ 50 * (4 / 5) * (R * (1 + 1 / 2 ^ 52)) + R / 2 ^ 101 ≤ R / 2 ^ 49 := by
      have : 1 / 2 ^ 50 * (4 / 5) * (R * (1 + 1 / 2 ^ 52)) + R / 2 ^ 101 =
          R * (1 / 2 ^ 50 * (4 / 5) * (1 + 1 / 2 ^ 52) + 1 / 2 ^ 101) := by ring
      rw [this]
      have h5 : (1 : ℝ) / 2 ^ 50 * (4 / 5) * (1 + 1 / 2 ^ 52) + 1 / 2 ^ 101 ≤ 1 / 2 ^ 49 := by
        norm_num
      have := mul_le_mul_of_nonneg_left h5 hR0.le
      linarith [(by ring : R * (1 / 2 ^ 49) = R / 2 ^ 49)]
    linarith
  · have h1 := abs_add_le (z + (S - vl * z) * z - 1 / (vx + vl))
      (value zl.toBits - (S - vl * z) * z)
    rw [show z + (S - vl * z) * z - 1 / (vx + vl) + (value zl.toBits - (S - vl * z) * z) =
      z + value zl.toBits - 1 / (vx + vl) by ring] at h1
    have : R / 2 ^ 100 + R / 2 ^ 101 ≤ R / 2 ^ 98 := by
      have : R / 2 ^ 100 + R / 2 ^ 101 = R * (1 / 2 ^ 100 + 1 / 2 ^ 101) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) / 2 ^ 100 + 1 / 2 ^ 101 ≤
        1 / 2 ^ 98) hR0.le
      linarith [(by ring : R * (1 / 2 ^ 98) = R / 2 ^ 98)]
    linarith

#print axioms recip_dd

end Library.Numerics.Float64.Lgamma.LgammaAsymRecip
