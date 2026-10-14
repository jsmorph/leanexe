import Verified.Examples.TgammaSinpidSum

/-!
Bounds of the low parts of `Tgamma`'s double-double operations in units of `2^-53` of the high
part.  `TgammaDD` bounds a rounding error by `2^-52` of the result, which is enough for the error of
a sum, but the bound `|sl| ≤ |sh|/2^50` on the result of `Tgamma.asSinpid` needs the factor
`2^-53` of round-to-nearest.  `rel_of_approx` turns an error bound relative to the exact value into
one relative to the rounded result.  With it, the low part of `fastTwoSum` is at most `2^-53` of the
high part (`fts_low`), and the low parts of `fastSum`, `mulDD`, and `mulDDD` are the sums of their
terms with the rounding error of the high part (`fastSum_low`, `mulDD_low`, `mulDDD_low`), up to
factors `1 + 2^-50` and terms below `2^-1070`.
-/

namespace Verified.Examples.TgammaSinpidLow
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaSinpidSum

set_option exponentiation.threshold 4096

/-- An error bound relative to the exact value bounds the error relative to the result. -/
theorem rel_of_approx (o v E : ℝ) (hE : 0 ≤ E) (h : |o - v| ≤ |v| / 2 ^ 53 + E) :
    |o - v| ≤ |o| / 2 ^ 53 * (1 + 1 / 2 ^ 52) + 2 * E := by
  have h1 : |v| ≤ |o| + |o - v| := by
    have := abs_sub_abs_le_abs_sub o v
    have := abs_sub_comm o v
    have := abs_sub_abs_le_abs_sub v o
    linarith
  have ho : 0 ≤ |o| := abs_nonneg o
  linarith [(by norm_num : (0 : ℝ) < 1 / 2 ^ 105)]

/-- **The low part of `fastTwoSum`** is at most `2^-53` of the high part, whenever the pair is exact. -/
theorem fts_low (x y : Float) (hx : Finite x.toBits) (hy : Finite y.toBits)
    (hlim : |value x.toBits + value y.toBits| < 2 ^ 1023)
    (hsum : value (fastTwoSum x y).1.toBits + value (fastTwoSum x y).2.toBits =
      value x.toBits + value y.toBits) :
    |value (fastTwoSum x y).2.toBits| ≤
      |value (fastTwoSum x y).1.toBits| / 2 ^ 53 * (1 + 1 / 2 ^ 52) := by
  have ha := fapprox_add (fapprox_self x hx) (fapprox_self y hy) |value x.toBits + value y.toBits|
    (by simp) hlim
  have h1 : (fastTwoSum x y).1 = x + y := rfl
  have h2 := ha.2
  rw [← h1] at h2
  have h3 := rel_of_approx (value (fastTwoSum x y).1.toBits) (value x.toBits + value y.toBits) 0
    le_rfl (by linarith)
  have h4 : value (fastTwoSum x y).2.toBits =
      -(value (fastTwoSum x y).1.toBits - (value x.toBits + value y.toBits)) := by linarith
  rw [h4, abs_neg]
  linarith

/-- The pair of `fastTwoSum` is exact for `|y| ≤ |x|` or `x = 0`. -/
theorem fts_exact (x y : Float) (hx : Finite x.toBits) (hy : Finite y.toBits)
    (hxy : |value y.toBits| ≤ |value x.toBits| ∨ value x.toBits = 0)
    (hlim : |value x.toBits| < 2 ^ 898) (hlimy : |value y.toBits| < 2 ^ 898) :
    Finite (fastTwoSum x y).1.toBits ∧ Finite (fastTwoSum x y).2.toBits ∧
      value (fastTwoSum x y).1.toBits + value (fastTwoSum x y).2.toBits =
        value x.toBits + value y.toBits := by
  rcases hxy with h | h0
  · obtain ⟨h1, h2, h3, -⟩ := fastTwoSum_spec x y hx hy h (hlim.trans (by norm_num))
    exact ⟨h1, h2, h3⟩
  · obtain ⟨h1, h2, h3, h4⟩ := fastTwoSum_zero x y hx hy h0 hlimy
    exact ⟨h1, h2, by rw [h3, h4, h0]; ring⟩

/-- **The low part of `fastSum`**: the low parts and the rounding error of the high part. -/
theorem fastSum_low (xh xl yh yl : Float) (hxh : Finite xh.toBits) (hxl : Finite xl.toBits)
    (hyh : Finite yh.toBits) (hyl : Finite yl.toBits)
    (hxy : |value yh.toBits| ≤ |value xh.toBits| ∨ value xh.toBits = 0)
    (hlim : |value xh.toBits| < 2 ^ 898) (hlimy : |value yh.toBits| < 2 ^ 898)
    (hxl1 : |value xl.toBits| ≤ 2 ^ 800) (hyl1 : |value yl.toBits| ≤ 2 ^ 800) :
    |value (fastSum xh xl yh yl).2.toBits| ≤
      (|value xl.toBits| + |value yl.toBits| +
        |value (fastSum xh xl yh yl).1.toBits| / 2 ^ 53 * (1 + 1 / 2 ^ 52)) * (1 + 1 / 2 ^ 51) := by
  obtain ⟨hsf, htf, hsum⟩ := fts_exact xh yh hxh hyh hxy hlim hlimy
  have ht := fts_low xh yh hxh hyh (by
    have := abs_add_le (value xh.toBits) (value yh.toBits)
    linarith [(by norm_num : (2 : ℝ) ^ 898 + 2 ^ 898 < 2 ^ 1023)]) hsum
  have hs1 : (fastSum xh xl yh yl).1 = (fastTwoSum xh yh).1 := by simp only [fastSum]
  have hs2 : (fastSum xh xl yh yl).2 = (xl + yl) + (fastTwoSum xh yh).2 := by simp only [fastSum]
  rw [hs1, hs2]
  obtain ⟨S, hS⟩ : ∃ v, v = |value (fastTwoSum xh yh).1.toBits| := ⟨_, rfl⟩
  rw [← hS] at ht ⊢
  have hS0 : 0 ≤ S := by rw [hS]; exact abs_nonneg _
  have hSb : S ≤ 2 ^ 900 := by
    have h1 := abs_sub_abs_le_abs_sub (value (fastTwoSum xh yh).1.toBits)
      (value (fastTwoSum xh yh).1.toBits + value (fastTwoSum xh yh).2.toBits)
    rw [sub_add_cancel_left, abs_neg, hsum] at h1
    have h2 := abs_add_le (value xh.toBits) (value yh.toBits)
    have h3 : |value (fastTwoSum xh yh).2.toBits| ≤ S := by
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 53 * (1 + 1 / 2 ^ 52) ≤ 1 / 2)]
    rw [← hS] at h1
    linarith [(by norm_num : (2 : ℝ) ^ 898 * 4 ≤ 2 ^ 900)]
  obtain ⟨T, hT⟩ : ∃ v, v = |value (fastTwoSum xh yh).2.toBits| := ⟨_, rfl⟩
  rw [← hT] at ht
  have hu := fapprox_add (fapprox_self xl hxl) (fapprox_self yl hyl)
    (|value xl.toBits| + |value yl.toBits|) (by simp only [add_zero]; exact abs_add_le _ _)
    (by linarith [(by norm_num : (2 : ℝ) ^ 800 + 2 ^ 800 < 2 ^ 1023)])
  have hT0 : 0 ≤ T := by rw [hT]; exact abs_nonneg _
  have hw := fapprox_add hu (fapprox_self _ htf)
    (|value xl.toBits| + |value yl.toBits| + T + (|value xl.toBits| + |value yl.toBits|))
    (by
      have h1 := abs_add_le (value xl.toBits + value yl.toBits) (value (fastTwoSum xh yh).2.toBits)
      have h2 := abs_add_le (value xl.toBits) (value yl.toBits)
      have h3 : (0 + 0 + (|value xl.toBits| + |value yl.toBits|) / 2 ^ 53) + 0 ≤
          |value xl.toBits| + |value yl.toBits| := by
        have := abs_nonneg (value xl.toBits); have := abs_nonneg (value yl.toBits)
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 53 ≤ 1)]
      rw [← hT] at h1
      linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 800 * 4 + 2 ^ 900 < 2 ^ 1023)])
  have h1 := hw.2
  have h2 := abs_sub_abs_le_abs_sub (value ((xl + yl) + (fastTwoSum xh yh).2).toBits)
    (value xl.toBits + value yl.toBits + value (fastTwoSum xh yh).2.toBits)
  have h3 := abs_add_le (value xl.toBits + value yl.toBits) (value (fastTwoSum xh yh).2.toBits)
  have h4 := abs_add_le (value xl.toBits) (value yl.toBits)
  rw [← hT] at h3
  have hx0 := abs_nonneg (value xl.toBits)
  have hy0 := abs_nonneg (value yl.toBits)
  linarith

/-- **The low part of `mulDDD`**: `cl x` and the rounding error of `ch x`. -/
theorem mulDDD_low (hF : FmaSpec.FmaNearest) (x ch cl : Float) (hx : Finite x.toBits)
    (hch : Finite ch.toBits) (hcl : Finite cl.toBits)
    (hH : |value ch.toBits| * |value x.toBits| ≤ 2 ^ 900)
    (hL : |value cl.toBits| * |value x.toBits| ≤ 2 ^ 900) :
    |value (mulDDD x ch cl).2.toBits| ≤
      (|value cl.toBits| * |value x.toBits| + |value (mulDDD x ch cl).1.toBits| / 2 ^ 53) *
        (1 + 1 / 2 ^ 50) + 1 / 2 ^ 1071 ∧
      |value ch.toBits| * |value x.toBits| * (1 - 1 / 2 ^ 53) - 1 / 2 ^ 1075 ≤
        |value (mulDDD x ch cl).1.toBits| := by
  have h1 : (mulDDD x ch cl).1 = ch * x := rfl
  have h2 : (mulDDD x ch cl).2 = cl * x + Fma.fma ch x (-(ch * x)) := rfl
  rw [h1, h2]
  have hP : |value ch.toBits| * |value x.toBits| = |value ch.toBits * value x.toBits| := (abs_mul _ _).symm
  -- `a = ch x`
  have ha0 := fapprox_mul (fapprox_self ch hch) (fapprox_self x hx) |value ch.toBits| |value x.toBits| le_rfl le_rfl
    (|value ch.toBits| * |value x.toBits|) (by simp) (by linarith [(by norm_num : (2 : ℝ) ^ 900 < 2 ^ 1022)])
  have ha : |value (ch * x).toBits - value ch.toBits * value x.toBits| ≤ |value ch.toBits * value x.toBits| / 2 ^ 53 + 1 / 2 ^ 1075 := by
    have := ha0.2; rw [← hP]; linarith
  have hre := rel_of_approx (value (ch * x).toBits) (value ch.toBits * value x.toBits) (1 / 2 ^ 1075) (by norm_num) ha
  have hlow : |value ch.toBits| * |value x.toBits| * (1 - 1 / 2 ^ 53) - 1 / 2 ^ 1075 ≤ |value (ch * x).toBits| := by
    have := abs_sub_abs_le_abs_sub (value ch.toBits * value x.toBits) (value (ch * x).toBits)
    rw [abs_sub_comm] at this
    rw [hP]; linarith [abs_nonneg (value ch.toBits * value x.toBits)]
  refine ⟨?_, hlow⟩
  -- `-a` is exact
  have hna := fapprox_neg (fapprox_self (ch * x) ha0.1)
  have hnav : value (-(ch * x)).toBits = -value (ch * x).toBits := by
    have h0 := abs_nonpos_iff.mp hna.2
    linarith
  have hSb : |value ch.toBits * value x.toBits + value (-(ch * x)).toBits| ≤ 2 ^ 1000 := by
    rw [hnav, ← sub_eq_add_neg]
    have : |value ch.toBits * value x.toBits - value (ch * x).toBits| ≤ |value ch.toBits * value x.toBits| / 2 ^ 53 + 1 / 2 ^ 1075 := by rw [abs_sub_comm]; exact ha
    rw [← hP] at this
    linarith [(by norm_num : (2 : ℝ) ^ 900 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 2 ^ 1000)]
  have hf := fma_approx hF ch x (-(ch * x)) hch hx hna.1 hSb
  rw [hnav, ← sub_eq_add_neg] at hf
  -- `g = cl x`
  have hg0 := fapprox_mul (fapprox_self cl hcl) (fapprox_self x hx) |value cl.toBits| |value x.toBits| le_rfl le_rfl
    (|value cl.toBits| * |value x.toBits|) (by simp) (by linarith [(by norm_num : (2 : ℝ) ^ 900 < 2 ^ 1022)])
  have hgb : |value (cl * x).toBits| ≤ |value cl.toBits| * |value x.toBits| * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 := by
    have h1 := hg0.2
    have h2 := abs_sub_abs_le_abs_sub (value (cl * x).toBits) (value cl.toBits * value x.toBits)
    rw [abs_mul] at h2
    simp only [mul_zero, zero_mul, add_zero, zero_add] at h1
    linarith
  have hfb : |value (Fma.fma ch x (-(ch * x))).toBits| ≤ |value (ch * x).toBits| / 2 ^ 53 * (1 + 1 / 2 ^ 52) * (1 + 1 / 2 ^ 53) + 4 / 2 ^ 1075 := by
    have h1 := hf.2
    have h2 := abs_sub_abs_le_abs_sub (value (Fma.fma ch x (-(ch * x))).toBits) (value ch.toBits * value x.toBits - value (ch * x).toBits)
    have h3 : |value ch.toBits * value x.toBits - value (ch * x).toBits| ≤ |value (ch * x).toBits| / 2 ^ 53 * (1 + 1 / 2 ^ 52) + 2 * (1 / 2 ^ 1075) := by
      rw [abs_sub_comm]; exact hre
    linarith [abs_nonneg (value ch.toBits * value x.toBits - value (ch * x).toBits)]
  have hvab : |value (ch * x).toBits| ≤ 2 ^ 901 := by
    have := abs_sub_abs_le_abs_sub (value (ch * x).toBits) (value ch.toBits * value x.toBits)
    rw [← hP] at this ha
    linarith [(by norm_num : (2 : ℝ) ^ 900 + 2 ^ 900 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 2 ^ 901)]
  have hw := fapprox_add (fapprox_self _ hg0.1) (fapprox_self _ hf.1) (|value (cl * x).toBits| + |value (Fma.fma ch x (-(ch * x))).toBits|)
    (by simp only [add_zero]; exact abs_add_le _ _) (by
      linarith [abs_nonneg (value (ch * x).toBits),
        (by norm_num : (2 : ℝ) ^ 900 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 +
          (2 ^ 901 / 2 ^ 53 * (1 + 1 / 2 ^ 52) * (1 + 1 / 2 ^ 53) + 4 / 2 ^ 1075) < 2 ^ 1023)])
  have h1 := hw.2
  have h2 := abs_sub_abs_le_abs_sub (value (cl * x + Fma.fma ch x (-(ch * x))).toBits) (value (cl * x).toBits + value (Fma.fma ch x (-(ch * x))).toBits)
  have h3 := abs_add_le (value (cl * x).toBits) (value (Fma.fma ch x (-(ch * x))).toBits)
  have hva0 := abs_nonneg (value (ch * x).toBits)
  have hp0 : 0 ≤ |value cl.toBits| * |value x.toBits| := by positivity
  linarith

/-- **The low part of `mulDD`**: `ch xl + cl xh` and the rounding error of `ch xh`. -/
theorem mulDD_low (hF : FmaSpec.FmaNearest) (xh xl ch cl : Float) (hxh : Finite xh.toBits)
    (hxl : Finite xl.toBits) (hch : Finite ch.toBits) (hcl : Finite cl.toBits)
    (hH : |value ch.toBits| * |value xh.toBits| ≤ 2 ^ 900)
    (hP1 : |value ch.toBits| * |value xl.toBits| ≤ 2 ^ 800)
    (hP2 : |value cl.toBits| * |value xh.toBits| ≤ 2 ^ 800) :
    |value (mulDD xh xl ch cl).2.toBits| ≤
      (|value ch.toBits| * |value xl.toBits| + |value cl.toBits| * |value xh.toBits| +
        |value (mulDD xh xl ch cl).1.toBits| / 2 ^ 53) * (1 + 1 / 2 ^ 50) + 1 / 2 ^ 1070 := by
  have h1 : (mulDD xh xl ch cl).1 = ch * xh := rfl
  have h2 : (mulDD xh xl ch cl).2 = (ch * xl + cl * xh) + Fma.fma ch xh (-(ch * xh)) := rfl
  rw [h1, h2]
  have hP : |value ch.toBits| * |value xh.toBits| = |value ch.toBits * value xh.toBits| := (abs_mul _ _).symm
  have ha0 := fapprox_mul (fapprox_self ch hch) (fapprox_self xh hxh) |value ch.toBits| |value xh.toBits| le_rfl le_rfl
    (|value ch.toBits| * |value xh.toBits|) (by simp) (by linarith [(by norm_num : (2 : ℝ) ^ 900 < 2 ^ 1022)])
  have ha : |value (ch * xh).toBits - value ch.toBits * value xh.toBits| ≤ |value ch.toBits * value xh.toBits| / 2 ^ 53 + 1 / 2 ^ 1075 := by
    have := ha0.2; rw [← hP]; linarith
  have hre := rel_of_approx (value (ch * xh).toBits) (value ch.toBits * value xh.toBits) (1 / 2 ^ 1075) (by norm_num) ha
  have hna := fapprox_neg (fapprox_self (ch * xh) ha0.1)
  have hnav : value (-(ch * xh)).toBits = -value (ch * xh).toBits := by
    have h0 := abs_nonpos_iff.mp hna.2
    linarith
  have hSb : |value ch.toBits * value xh.toBits + value (-(ch * xh)).toBits| ≤ 2 ^ 1000 := by
    rw [hnav, ← sub_eq_add_neg]
    have : |value ch.toBits * value xh.toBits - value (ch * xh).toBits| ≤ |value ch.toBits * value xh.toBits| / 2 ^ 53 + 1 / 2 ^ 1075 := by rw [abs_sub_comm]; exact ha
    rw [← hP] at this
    linarith [(by norm_num : (2 : ℝ) ^ 900 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 2 ^ 1000)]
  have hf := fma_approx hF ch xh (-(ch * xh)) hch hxh hna.1 hSb
  rw [hnav, ← sub_eq_add_neg] at hf
  have hfb : |value (Fma.fma ch xh (-(ch * xh))).toBits| ≤ |value (ch * xh).toBits| / 2 ^ 53 * (1 + 1 / 2 ^ 52) * (1 + 1 / 2 ^ 53) + 4 / 2 ^ 1075 := by
    have h1 := hf.2
    have h2 := abs_sub_abs_le_abs_sub (value (Fma.fma ch xh (-(ch * xh))).toBits) (value ch.toBits * value xh.toBits - value (ch * xh).toBits)
    have h3 : |value ch.toBits * value xh.toBits - value (ch * xh).toBits| ≤ |value (ch * xh).toBits| / 2 ^ 53 * (1 + 1 / 2 ^ 52) + 2 * (1 / 2 ^ 1075) := by
      rw [abs_sub_comm]; exact hre
    linarith [abs_nonneg (value ch.toBits * value xh.toBits - value (ch * xh).toBits)]
  have hvab : |value (ch * xh).toBits| ≤ 2 ^ 901 := by
    have := abs_sub_abs_le_abs_sub (value (ch * xh).toBits) (value ch.toBits * value xh.toBits)
    rw [← hP] at this ha
    linarith [(by norm_num : (2 : ℝ) ^ 900 + 2 ^ 900 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 2 ^ 901)]
  -- `u = ch xl + cl xh`
  have hu1 := fapprox_mul (fapprox_self ch hch) (fapprox_self xl hxl) |value ch.toBits| |value xl.toBits| le_rfl le_rfl
    (|value ch.toBits| * |value xl.toBits|) (by simp) (by linarith [(by norm_num : (2 : ℝ) ^ 800 < 2 ^ 1022)])
  have hu2 := fapprox_mul (fapprox_self cl hcl) (fapprox_self xh hxh) |value cl.toBits| |value xh.toBits| le_rfl le_rfl
    (|value cl.toBits| * |value xh.toBits|) (by simp) (by linarith [(by norm_num : (2 : ℝ) ^ 800 < 2 ^ 1022)])
  have hb1 : |value (ch * xl).toBits| ≤ |value ch.toBits| * |value xl.toBits| * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 := by
    have h1 := hu1.2
    have h2 := abs_sub_abs_le_abs_sub (value (ch * xl).toBits) (value ch.toBits * value xl.toBits)
    rw [abs_mul] at h2
    simp only [mul_zero, zero_mul, add_zero, zero_add] at h1
    linarith
  have hb2 : |value (cl * xh).toBits| ≤ |value cl.toBits| * |value xh.toBits| * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 := by
    have h1 := hu2.2
    have h2 := abs_sub_abs_le_abs_sub (value (cl * xh).toBits) (value cl.toBits * value xh.toBits)
    rw [abs_mul] at h2
    simp only [mul_zero, zero_mul, add_zero, zero_add] at h1
    linarith
  have hp1 : 0 ≤ |value ch.toBits| * |value xl.toBits| := by positivity
  have hp2 : 0 ≤ |value cl.toBits| * |value xh.toBits| := by positivity
  have hu := fapprox_add (fapprox_self _ hu1.1) (fapprox_self _ hu2.1) (|value (ch * xl).toBits| + |value (cl * xh).toBits|)
    (by simp only [add_zero]; exact abs_add_le _ _)
    (by linarith [(by norm_num : (2 : ℝ) ^ 800 * (1 + 1 / 2 ^ 53) * 2 + 2 / 2 ^ 1075 < 2 ^ 1023)])
  have hub : |value (ch * xl + cl * xh).toBits| ≤ (|value (ch * xl).toBits| + |value (cl * xh).toBits|) * (1 + 1 / 2 ^ 53) := by
    have h1 := hu.2
    have h2 := abs_sub_abs_le_abs_sub (value (ch * xl + cl * xh).toBits) (value (ch * xl).toBits + value (cl * xh).toBits)
    have h3 := abs_add_le (value (ch * xl).toBits) (value (cl * xh).toBits)
    simp only [zero_add] at h1
    linarith [abs_nonneg (value (ch * xl).toBits), abs_nonneg (value (cl * xh).toBits)]
  have hw := fapprox_add (fapprox_self _ hu.1) (fapprox_self _ hf.1) (|value (ch * xl + cl * xh).toBits| + |value (Fma.fma ch xh (-(ch * xh))).toBits|)
    (by simp only [add_zero]; exact abs_add_le _ _) (by
      linarith [abs_nonneg (value (ch * xh).toBits), abs_nonneg (value (ch * xl).toBits), abs_nonneg (value (cl * xh).toBits),
        (by norm_num : ((2 : ℝ) ^ 800 * (1 + 1 / 2 ^ 53) * 2 + 2 / 2 ^ 1075) * (1 + 1 / 2 ^ 53) +
          (2 ^ 901 / 2 ^ 53 * (1 + 1 / 2 ^ 52) * (1 + 1 / 2 ^ 53) + 4 / 2 ^ 1075) < 2 ^ 1023)])
  have h1 := hw.2
  have h2 := abs_sub_abs_le_abs_sub (value ((ch * xl + cl * xh) + Fma.fma ch xh (-(ch * xh))).toBits)
    (value (ch * xl + cl * xh).toBits + value (Fma.fma ch xh (-(ch * xh))).toBits)
  have h3 := abs_add_le (value (ch * xl + cl * xh).toBits) (value (Fma.fma ch xh (-(ch * xh))).toBits)
  have hva0 := abs_nonneg (value (ch * xh).toBits)
  linarith

#print axioms fastSum_low
#print axioms mulDDD_low
#print axioms mulDD_low

end Verified.Examples.TgammaSinpidLow
