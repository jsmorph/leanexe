import Verified.Examples.AsinTheoremSupport

/-!
The rational function of `Asin.asinRatio`, `t (pS0 + ... + pS5 t ^ 5)/(1 + qS1 t + ... + qS4 t ^ 4)`
in the order of `e_asin.c`, as `F64Approx.SApprox` chains for seven ranges of `t`.  Each partial
sum of the two Horner schemes has a bound over its range that the kernel checks with
`PolyBound.check`, which keeps the bounds near the true magnitudes of the alternating sums, and
the denominator's lower bound comes from the same check.  The input `t` may carry a relative
error, as `x * x` does.
-/

namespace Verified.Examples.AsinTheoremRatio
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound AsinTheoremSupport

set_option exponentiation.threshold 4096

theorem ratio_S1 (t : Float) (vt σ : ℝ) (ht : FSApprox t vt σ 1 ((10001 / 10000) / 2 ^ 53))
    (hlo : 0 ≤ vt) (hhi : vt ≤ (1 / 8)) (hσ : σ ≤ (1 / 8)) (hσ0 : 1 / 2 ^ 54 ≤ σ) :
    FSApprox (Asin.asinRatio t) (vt * (value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))) / (1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))))) σ (2287 / 10000)
      ((17227 / 10000) / 2 ^ 53) := by
  have hσp : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hσ1 : σ ≤ 1 := hσ.trans (by norm_num)
  have hk1 : σ ≤ (1 / 8) * 1 := by rw [mul_one]; exact hσ
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hησ : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * σ := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 54) ≤ 1 / 2 ^ 960 * σ :=
      mul_le_mul_of_nonneg_left hσ0 (by positivity)
    norm_num at this ⊢
    linarith
  have hησ' : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * 1) := by rw [mul_one]; exact hησ
  have one1 := one_sapprox
  have tk := (ht.rescale 1 (1 / 8) one_pos le_rfl hk1).mono
    (M' := (1 / 8)) (e' := (1251 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c5 := fsapprox_const 0x3F023DE10DFDF709 (by decide +kernel) (((87 / 2500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have pr4 := (fsapprox_mul tk c5 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (87 / 20000000)) (e' := (1 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq4 := pr4.rescale 1 1 one_pos le_rfl (by norm_num)
  have c4 := fsapprox_const 0x3F49EFE07501B288 (by decide +kernel) (((39577 / 50000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb4 : |value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709| ≤ (79599 / 100000000) * 1 := by
    have h := poly_bound [ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 8) (79599 / 100000000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a4 := (fsapprox_add c4 pq4 (79599 / 100000000) hb4 (by norm_num)).mono
    (M' := (79599 / 100000000)) (e' := (9 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr3 := (fsapprox_mul tk a4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (199 / 2000000)) (e' := (1 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq3 := pr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have c3 := fsapprox_const 0xBFA48228B5688F3B (by decide +kernel) (((401 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb3 : |value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)| ≤ (401 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 8) (401 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a3 := (fsapprox_add c3 pq3 (401 / 10000) hb3 (by norm_num)).mono
    (M' := (401 / 10000)) (e' := (203 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr2 := (fsapprox_mul tk a3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (401 / 80000)) (e' := (19 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq2 := pr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have c2 := fsapprox_const 0x3FC9C1550E884455 (by decide +kernel) (((2013 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb2 : |value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))| ≤ (2013 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 8) (2013 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a2 := (fsapprox_add c2 pq2 (2013 / 10000) hb2 (by norm_num)).mono
    (M' := (2013 / 10000)) (e' := (1083 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr1 := (fsapprox_mul tk a2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (63 / 2500)) (e' := (31 / 400) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq1 := pr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have c1 := fsapprox_const 0xBFD4D61203EB6F7D (by decide +kernel) (((407 / 1250) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb1 : |value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)))| ≤ (407 / 1250) * 1 := by
    have h := poly_bound [ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 8) (407 / 1250) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a1 := (fsapprox_add c1 pq1 (407 / 1250) hb1 (by norm_num)).mono
    (M' := (407 / 1250)) (e' := (252 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr0 := (fsapprox_mul tk a1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (407 / 10000)) (e' := (1319 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq0 := pr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have c0 := fsapprox_const 0x3FC5555555555555 (by decide +kernel) (((1667 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb0 : |value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))| ≤ (417 / 2500) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC5555555555555, ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 8) (417 / 2500) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a0 := (fsapprox_add c0 pq0 (417 / 2500) hb0 (by norm_num)).mono
    (M' := (417 / 2500)) (e' := (747 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have p0 := (fsapprox_mul ht a0 (1 / 2 ^ 960) hησ' (by norm_num)).mono
    (M' := (417 / 2500)) (e' := (253 / 400) / 2 ^ 53) (by norm_num) (by norm_num)
  have p1 := p0.rescale σ 1 hσp hσ1 (by rw [mul_one, one_mul])
  have d4 := fsapprox_const 0x3FB3B8C5B12E9282 (by decide +kernel) (((771 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have qr3 := (fsapprox_mul tk d4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (771 / 80000)) (e' := (193 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq3 := qr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have d3c := fsapprox_const 0xBFE6066C1B8D0159 (by decide +kernel) (((6883 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq3 : |value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282| ≤ (6883 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 8) (6883 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d3 := (fsapprox_add d3c qq3 (6883 / 10000) hq3 (by norm_num)).mono
    (M' := (6883 / 10000)) (e' := (7077 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr2 := (fsapprox_mul tk d3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (861 / 10000)) (e' := (2607 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq2 := qr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have d2c := fsapprox_const 0x40002AE59C598AC8 (by decide +kernel) (((2021 / 1000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq2 : |value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)| ≤ (20211 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 8) (20211 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d2 := (fsapprox_add d2c qq2 (20211 / 10000) hq2 (by norm_num)).mono
    (M' := (20211 / 10000)) (e' := (22819 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr1 := (fsapprox_mul tk d2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (2527 / 10000)) (e' := (1977 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq1 := qr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have d1c := fsapprox_const 0xC0033A271C8A2D4B (by decide +kernel) (((12017 / 5000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq1 : |value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))| ≤ (24037 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 8) (24037 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d1 := (fsapprox_add d1c qq1 (24037 / 10000) hq1 (by norm_num)).mono
    (M' := (24037 / 10000)) (e' := (15973 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr0 := (fsapprox_mul tk d1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (601 / 2000)) (e' := (2001 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq0 := qr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have hq0 : |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| ≤ (10003 / 10000) * 1 := by
    have h := poly_bound [1, ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 8) (10003 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have q0 := (fsapprox_add one1 qq0 (10003 / 10000) hq0 (by norm_num)).mono
    (M' := (10003 / 10000)) (e' := (20009 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hmq : (145911 / 200000) ≤ |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| := by
    have h := poly_bound [(135087 / 1000000), ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 8) (67679 / 500000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    push_cast at h
    have h2 := (abs_le.mp h).1
    rw [abs_of_pos (by norm_num at h2 ⊢; linarith)]
    norm_num at h2 ⊢; linarith
  have r0 := (fsapprox_div p1 q0 (145911 / 200000) hmq (by norm_num) (1 / 2 ^ 960) hησ (by norm_num)).mono
    (M' := (2287 / 10000)) (e' := (17227 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  exact r0

theorem ratio_S2 (t : Float) (vt σ : ℝ) (ht : FSApprox t vt σ 1 ((10001 / 10000) / 2 ^ 53))
    (hlo : (1 / 8) ≤ vt) (hhi : vt ≤ (1 / 4)) (hσ : σ ≤ (1 / 4)) (hσ0 : 1 / 2 ^ 54 ≤ σ) :
    FSApprox (Asin.asinRatio t) (vt * (value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))) / (1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))))) σ (627 / 2500)
      ((28561 / 10000) / 2 ^ 53) := by
  have hσp : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hσ1 : σ ≤ 1 := hσ.trans (by norm_num)
  have hk1 : σ ≤ (1 / 4) * 1 := by rw [mul_one]; exact hσ
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hησ : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * σ := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 54) ≤ 1 / 2 ^ 960 * σ :=
      mul_le_mul_of_nonneg_left hσ0 (by positivity)
    norm_num at this ⊢
    linarith
  have hησ' : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * 1) := by rw [mul_one]; exact hησ
  have one1 := one_sapprox
  have tk := (ht.rescale 1 (1 / 4) one_pos le_rfl hk1).mono
    (M' := (1 / 4)) (e' := (2501 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have c5 := fsapprox_const 0x3F023DE10DFDF709 (by decide +kernel) (((87 / 2500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have pr4 := (fsapprox_mul tk c5 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (87 / 10000000)) (e' := (1 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq4 := pr4.rescale 1 1 one_pos le_rfl (by norm_num)
  have c4 := fsapprox_const 0x3F49EFE07501B288 (by decide +kernel) (((39577 / 50000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb4 : |value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709| ≤ (40017 / 50000000) * 1 := by
    have h := poly_bound [ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 8) (1 / 4) (40017 / 50000000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a4 := (fsapprox_add c4 pq4 (40017 / 50000000) hb4 (by norm_num)).mono
    (M' := (40017 / 50000000)) (e' := (1 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr3 := (fsapprox_mul tk a4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (20009 / 100000000)) (e' := (7 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq3 := pr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have c3 := fsapprox_const 0xBFA48228B5688F3B (by decide +kernel) (((401 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb3 : |value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)| ≤ (1 / 25) * 1 := by
    have h := poly_bound [ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 8) (1 / 4) (1 / 25) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a3 := (fsapprox_add c3 pq3 (1 / 25) hb3 (by norm_num)).mono
    (M' := (1 / 25)) (e' := (51 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr2 := (fsapprox_mul tk a3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (1 / 100)) (e' := (303 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq2 := pr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have c2 := fsapprox_const 0x3FC9C1550E884455 (by decide +kernel) (((2013 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb2 : |value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))| ≤ (1963 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 8) (1 / 4) (1963 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a2 := (fsapprox_add c2 pq2 (1963 / 10000) hb2 (by norm_num)).mono
    (M' := (1963 / 10000)) (e' := (2267 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr1 := (fsapprox_mul tk a2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (491 / 10000)) (e' := (1549 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq1 := pr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have c1 := fsapprox_const 0xBFD4D61203EB6F7D (by decide +kernel) (((407 / 1250) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb1 : |value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)))| ≤ (3011 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 8) (1 / 4) (3011 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a1 := (fsapprox_add c1 pq1 (3011 / 10000) hb1 (by norm_num)).mono
    (M' := (3011 / 10000)) (e' := (4561 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr0 := (fsapprox_mul tk a1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (753 / 10000)) (e' := (2647 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq0 := pr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have c0 := fsapprox_const 0x3FC5555555555555 (by decide +kernel) (((1667 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb0 : |value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))| ≤ (1291 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC5555555555555, ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 8) (1 / 4) (1291 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a0 := (fsapprox_add c0 pq0 (1291 / 10000) hb0 (by norm_num)).mono
    (M' := (1291 / 10000)) (e' := (3939 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p0 := (fsapprox_mul ht a0 (1 / 2 ^ 960) hησ' (by norm_num)).mono
    (M' := (1291 / 10000)) (e' := (3261 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p1 := p0.rescale σ 1 hσp hσ1 (by rw [mul_one, one_mul])
  have d4 := fsapprox_const 0x3FB3B8C5B12E9282 (by decide +kernel) (((771 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have qr3 := (fsapprox_mul tk d4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (193 / 10000)) (e' := (193 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq3 := qr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have d3c := fsapprox_const 0xBFE6066C1B8D0159 (by decide +kernel) (((6883 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq3 : |value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282| ≤ (6787 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 8) (1 / 4) (6787 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d3 := (fsapprox_add d3c qq3 (6787 / 10000) hq3 (by norm_num)).mono
    (M' := (6787 / 10000)) (e' := (3587 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr2 := (fsapprox_mul tk d3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (1697 / 10000)) (e' := (1297 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq2 := qr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have d2c := fsapprox_const 0x40002AE59C598AC8 (by decide +kernel) (((2021 / 1000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq2 : |value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)| ≤ (9681 / 5000) * 1 := by
    have h := poly_bound [ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 8) (1 / 4) (9681 / 5000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d2 := (fsapprox_add d2c qq2 (9681 / 5000) hq2 (by norm_num)).mono
    (M' := (9681 / 5000)) (e' := (24551 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr1 := (fsapprox_mul tk d2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (4841 / 10000)) (e' := (15821 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq1 := qr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have d1c := fsapprox_const 0xC0033A271C8A2D4B (by decide +kernel) (((12017 / 5000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq1 : |value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))| ≤ (21617 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 8) (1 / 4) (21617 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d1 := (fsapprox_add d1c qq1 (21617 / 10000) hq1 (by norm_num)).mono
    (M' := (21617 / 10000)) (e' := (37439 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr0 := (fsapprox_mul tk d1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (1081 / 2000)) (e' := (20171 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq0 := qr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have hq0 : |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| ≤ (7301 / 10000) * 1 := by
    have h := poly_bound [1, ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 8) (1 / 4) (7301 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have q0 := (fsapprox_add one1 qq0 (7301 / 10000) hq0 (by norm_num)).mono
    (M' := (7301 / 10000)) (e' := (27473 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hmq : (514791 / 1000000) ≤ |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| := by
    have h := poly_bound [(377583 / 1000000), ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 8) (1 / 4) (53813 / 500000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    push_cast at h
    have h2 := (abs_le.mp h).1
    rw [abs_of_pos (by norm_num at h2 ⊢; linarith)]
    norm_num at h2 ⊢; linarith
  have r0 := (fsapprox_div p1 q0 (514791 / 1000000) hmq (by norm_num) (1 / 2 ^ 960) hησ (by norm_num)).mono
    (M' := (627 / 2500)) (e' := (28561 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  exact r0

theorem ratio_A1 (t : Float) (vt σ : ℝ) (ht : FSApprox t vt σ 1 (0 / 2 ^ 53))
    (hlo : (1 / 5) ≤ vt) (hhi : vt ≤ (1 / 4)) (hσ : σ ≤ (1 / 4)) (hσ0 : 1 / 2 ^ 54 ≤ σ) :
    FSApprox (Asin.asinRatio t) (vt * (value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))) / (1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))))) σ (2123 / 10000)
      ((1084 / 625) / 2 ^ 53) := by
  have hσp : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hσ1 : σ ≤ 1 := hσ.trans (by norm_num)
  have hk1 : σ ≤ (1 / 4) * 1 := by rw [mul_one]; exact hσ
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hησ : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * σ := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 54) ≤ 1 / 2 ^ 960 * σ :=
      mul_le_mul_of_nonneg_left hσ0 (by positivity)
    norm_num at this ⊢
    linarith
  have hησ' : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * 1) := by rw [mul_one]; exact hησ
  have one1 := one_sapprox
  have tk := (ht.rescale 1 (1 / 4) one_pos le_rfl hk1).mono
    (M' := (1 / 4)) (e' := 0 / 2 ^ 53) (by norm_num) (by norm_num)
  have c5 := fsapprox_const 0x3F023DE10DFDF709 (by decide +kernel) (((87 / 2500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have pr4 := (fsapprox_mul tk c5 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (87 / 10000000)) (e' := (1 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq4 := pr4.rescale 1 1 one_pos le_rfl (by norm_num)
  have c4 := fsapprox_const 0x3F49EFE07501B288 (by decide +kernel) (((39577 / 50000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb4 : |value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709| ≤ (40017 / 50000000) * 1 := by
    have h := poly_bound [ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 5) (1 / 4) (40017 / 50000000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a4 := (fsapprox_add c4 pq4 (40017 / 50000000) hb4 (by norm_num)).mono
    (M' := (40017 / 50000000)) (e' := (1 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr3 := (fsapprox_mul tk a4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (20009 / 100000000)) (e' := (1 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq3 := pr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have c3 := fsapprox_const 0xBFA48228B5688F3B (by decide +kernel) (((401 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb3 : |value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)| ≤ (399 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 5) (1 / 4) (399 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a3 := (fsapprox_add c3 pq3 (399 / 10000) hb3 (by norm_num)).mono
    (M' := (399 / 10000)) (e' := (81 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr2 := (fsapprox_mul tk a3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (399 / 40000)) (e' := (101 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq2 := pr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have c2 := fsapprox_const 0x3FC9C1550E884455 (by decide +kernel) (((2013 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb2 : |value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))| ≤ (1933 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 5) (1 / 4) (1933 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a2 := (fsapprox_add c2 pq2 (1933 / 10000) hb2 (by norm_num)).mono
    (M' := (1933 / 10000)) (e' := (267 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr1 := (fsapprox_mul tk a2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (121 / 2500)) (e' := (509 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq1 := pr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have c1 := fsapprox_const 0xBFD4D61203EB6F7D (by decide +kernel) (((407 / 1250) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb1 : |value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)))| ≤ (287 / 1000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 5) (1 / 4) (287 / 1000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a1 := (fsapprox_add c1 pq1 (287 / 1000) hb1 (by norm_num)).mono
    (M' := (287 / 1000)) (e' := (3889 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr0 := (fsapprox_mul tk a1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (359 / 5000)) (e' := (169 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq0 := pr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have c0 := fsapprox_const 0x3FC5555555555555 (by decide +kernel) (((1667 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb0 : |value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))| ≤ (1093 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC5555555555555, ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 5) (1 / 4) (1093 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a0 := (fsapprox_add c0 pq0 (1093 / 10000) hb0 (by norm_num)).mono
    (M' := (1093 / 10000)) (e' := (174 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  have p0 := (fsapprox_mul ht a0 (1 / 2 ^ 960) hησ' (by norm_num)).mono
    (M' := (1093 / 10000)) (e' := (1939 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p1 := p0.rescale σ 1 hσp hσ1 (by rw [mul_one, one_mul])
  have d4 := fsapprox_const 0x3FB3B8C5B12E9282 (by decide +kernel) (((771 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have qr3 := (fsapprox_mul tk d4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (193 / 10000)) (e' := (193 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq3 := qr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have d3c := fsapprox_const 0xBFE6066C1B8D0159 (by decide +kernel) (((6883 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq3 : |value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282| ≤ (6729 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 5) (1 / 4) (6729 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d3 := (fsapprox_add d3c qq3 (6729 / 10000) hq3 (by norm_num)).mono
    (M' := (6729 / 10000)) (e' := (6923 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr2 := (fsapprox_mul tk d3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (1683 / 10000)) (e' := (1707 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq2 := qr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have d2c := fsapprox_const 0x40002AE59C598AC8 (by decide +kernel) (((2021 / 1000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq2 : |value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)| ≤ (3773 / 2000) * 1 := by
    have h := poly_bound [ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 5) (1 / 4) (3773 / 2000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d2 := (fsapprox_add d2c qq2 (3773 / 2000) hq2 (by norm_num)).mono
    (M' := (3773 / 2000)) (e' := (557 / 250) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr1 := (fsapprox_mul tk d2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (4717 / 10000)) (e' := (10287 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq1 := qr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have d1c := fsapprox_const 0xC0033A271C8A2D4B (by decide +kernel) (((12017 / 5000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq1 : |value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))| ≤ (20263 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 5) (1 / 4) (20263 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d1 := (fsapprox_add d1c qq1 (20263 / 10000) hq1 (by norm_num)).mono
    (M' := (20263 / 10000)) (e' := (30551 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr0 := (fsapprox_mul tk d1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (2533 / 5000)) (e' := (794 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq0 := qr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have hq0 : |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| ≤ (5949 / 10000) * 1 := by
    have h := poly_bound [1, ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 5) (1 / 4) (5949 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have q0 := (fsapprox_add one1 qq0 (5949 / 10000) hq0 (by norm_num)).mono
    (M' := (5949 / 10000)) (e' := (9327 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hmq : (257463 / 500000) ≤ |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| := by
    have h := poly_bound [(445109 / 1000000), ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 5) (1 / 4) (7993 / 200000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    push_cast at h
    have h2 := (abs_le.mp h).1
    rw [abs_of_pos (by norm_num at h2 ⊢; linarith)]
    norm_num at h2 ⊢; linarith
  have r0 := (fsapprox_div p1 q0 (257463 / 500000) hmq (by norm_num) (1 / 2 ^ 960) hησ (by norm_num)).mono
    (M' := (2123 / 10000)) (e' := (1084 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  exact r0

theorem ratio_A2 (t : Float) (vt σ : ℝ) (ht : FSApprox t vt σ 1 (0 / 2 ^ 53))
    (hlo : (1 / 20) ≤ vt) (hhi : vt ≤ (1 / 5)) (hσ : σ ≤ (1 / 5)) (hσ0 : 1 / 2 ^ 54 ≤ σ) :
    FSApprox (Asin.asinRatio t) (vt * (value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))) / (1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))))) σ (2541 / 10000)
      ((18477 / 10000) / 2 ^ 53) := by
  have hσp : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hσ1 : σ ≤ 1 := hσ.trans (by norm_num)
  have hk1 : σ ≤ (1 / 5) * 1 := by rw [mul_one]; exact hσ
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hησ : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * σ := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 54) ≤ 1 / 2 ^ 960 * σ :=
      mul_le_mul_of_nonneg_left hσ0 (by positivity)
    norm_num at this ⊢
    linarith
  have hησ' : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * 1) := by rw [mul_one]; exact hησ
  have one1 := one_sapprox
  have tk := (ht.rescale 1 (1 / 5) one_pos le_rfl hk1).mono
    (M' := (1 / 5)) (e' := 0 / 2 ^ 53) (by norm_num) (by norm_num)
  have c5 := fsapprox_const 0x3F023DE10DFDF709 (by decide +kernel) (((87 / 2500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have pr4 := (fsapprox_mul tk c5 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (87 / 12500000)) (e' := (1 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq4 := pr4.rescale 1 1 one_pos le_rfl (by norm_num)
  have c4 := fsapprox_const 0x3F49EFE07501B288 (by decide +kernel) (((39577 / 50000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb4 : |value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709| ≤ (3993 / 5000000) * 1 := by
    have h := poly_bound [ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 20) (1 / 5) (3993 / 5000000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a4 := (fsapprox_add c4 pq4 (3993 / 5000000) hb4 (by norm_num)).mono
    (M' := (3993 / 5000000)) (e' := (9 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr3 := (fsapprox_mul tk a4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (3993 / 25000000)) (e' := (1 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq3 := pr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have c3 := fsapprox_const 0xBFA48228B5688F3B (by decide +kernel) (((401 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb3 : |value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)| ≤ (401 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 20) (1 / 5) (401 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a3 := (fsapprox_add c3 pq3 (401 / 10000) hb3 (by norm_num)).mono
    (M' := (401 / 10000)) (e' := (203 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr2 := (fsapprox_mul tk a3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (401 / 50000)) (e' := (81 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq2 := pr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have c2 := fsapprox_const 0x3FC9C1550E884455 (by decide +kernel) (((2013 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb2 : |value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))| ≤ (1993 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 20) (1 / 5) (1993 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a2 := (fsapprox_add c2 pq2 (1993 / 10000) hb2 (by norm_num)).mono
    (M' := (1993 / 10000)) (e' := (539 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr1 := (fsapprox_mul tk a2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (399 / 10000)) (e' := (83 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq1 := pr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have c1 := fsapprox_const 0xBFD4D61203EB6F7D (by decide +kernel) (((407 / 1250) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb1 : |value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)))| ≤ (3157 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 20) (1 / 5) (3157 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a1 := (fsapprox_add c1 pq1 (3157 / 10000) hb1 (by norm_num)).mono
    (M' := (3157 / 10000)) (e' := (997 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr0 := (fsapprox_mul tk a1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (79 / 1250)) (e' := (143 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq0 := pr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have c0 := fsapprox_const 0x3FC5555555555555 (by decide +kernel) (((1667 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb0 : |value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))| ≤ (151 / 1000) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC5555555555555, ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 20) (1 / 5) (151 / 1000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a0 := (fsapprox_add c0 pq0 (151 / 1000) hb0 (by norm_num)).mono
    (M' := (151 / 1000)) (e' := (2941 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p0 := (fsapprox_mul ht a0 (1 / 2 ^ 960) hησ' (by norm_num)).mono
    (M' := (151 / 1000)) (e' := (1113 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have p1 := p0.rescale σ 1 hσp hσ1 (by rw [mul_one, one_mul])
  have d4 := fsapprox_const 0x3FB3B8C5B12E9282 (by decide +kernel) (((771 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have qr3 := (fsapprox_mul tk d4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (31 / 2000)) (e' := (31 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq3 := qr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have d3c := fsapprox_const 0xBFE6066C1B8D0159 (by decide +kernel) (((6883 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq3 : |value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282| ≤ (1369 / 2000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 20) (1 / 5) (1369 / 2000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d3 := (fsapprox_add d3c qq3 (1369 / 2000) hq3 (by norm_num)).mono
    (M' := (1369 / 2000)) (e' := (7001 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr2 := (fsapprox_mul tk d3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (1369 / 10000)) (e' := (277 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq2 := qr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have d2c := fsapprox_const 0x40002AE59C598AC8 (by decide +kernel) (((2021 / 1000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq2 : |value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)| ≤ (19869 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 20) (1 / 5) (19869 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d2 := (fsapprox_add d2c qq2 (19869 / 10000) hq2 (by norm_num)).mono
    (M' := (19869 / 10000)) (e' := (283 / 125) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr1 := (fsapprox_mul tk d2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (1987 / 5000)) (e' := (4251 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq1 := qr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have d1c := fsapprox_const 0xC0033A271C8A2D4B (by decide +kernel) (((12017 / 5000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq1 : |value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))| ≤ (5761 / 2500) * 1 := by
    have h := poly_bound [ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 20) (1 / 5) (5761 / 2500) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d1 := (fsapprox_add d1c qq1 (5761 / 2500) hq1 (by norm_num)).mono
    (M' := (5761 / 2500)) (e' := (31547 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr0 := (fsapprox_mul tk d1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (4609 / 10000)) (e' := (10919 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq0 := qr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have hq0 : |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| ≤ (8851 / 10000) * 1 := by
    have h := poly_bound [1, ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 20) (1 / 5) (8851 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have q0 := (fsapprox_add one1 qq0 (8851 / 10000) hq0 (by norm_num)).mono
    (M' := (8851 / 10000)) (e' := (19771 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hmq : (148621 / 250000) ≤ |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| := by
    have h := poly_bound [(130107 / 500000), ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 20) (1 / 5) (72651 / 500000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    push_cast at h
    have h2 := (abs_le.mp h).1
    rw [abs_of_pos (by norm_num at h2 ⊢; linarith)]
    norm_num at h2 ⊢; linarith
  have r0 := (fsapprox_div p1 q0 (148621 / 250000) hmq (by norm_num) (1 / 2 ^ 960) hησ (by norm_num)).mono
    (M' := (2541 / 10000)) (e' := (18477 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  exact r0

theorem ratio_A3 (t : Float) (vt σ : ℝ) (ht : FSApprox t vt σ 1 (0 / 2 ^ 53))
    (hlo : (1 / 80) ≤ vt) (hhi : vt ≤ (1 / 20)) (hσ : σ ≤ (1 / 20)) (hσ0 : 1 / 2 ^ 54 ≤ σ) :
    FSApprox (Asin.asinRatio t) (vt * (value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))) / (1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))))) σ (23 / 125)
      ((843 / 1000) / 2 ^ 53) := by
  have hσp : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hσ1 : σ ≤ 1 := hσ.trans (by norm_num)
  have hk1 : σ ≤ (1 / 20) * 1 := by rw [mul_one]; exact hσ
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hησ : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * σ := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 54) ≤ 1 / 2 ^ 960 * σ :=
      mul_le_mul_of_nonneg_left hσ0 (by positivity)
    norm_num at this ⊢
    linarith
  have hησ' : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * 1) := by rw [mul_one]; exact hησ
  have one1 := one_sapprox
  have tk := (ht.rescale 1 (1 / 20) one_pos le_rfl hk1).mono
    (M' := (1 / 20)) (e' := 0 / 2 ^ 53) (by norm_num) (by norm_num)
  have c5 := fsapprox_const 0x3F023DE10DFDF709 (by decide +kernel) (((87 / 2500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have pr4 := (fsapprox_mul tk c5 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (87 / 50000000)) (e' := (1 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq4 := pr4.rescale 1 1 one_pos le_rfl (by norm_num)
  have c4 := fsapprox_const 0x3F49EFE07501B288 (by decide +kernel) (((39577 / 50000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb4 : |value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709| ≤ (39669 / 50000000) * 1 := by
    have h := poly_bound [ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 80) (1 / 20) (39669 / 50000000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a4 := (fsapprox_add c4 pq4 (39669 / 50000000) hb4 (by norm_num)).mono
    (M' := (39669 / 50000000)) (e' := (9 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr3 := (fsapprox_mul tk a4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (3967 / 100000000)) (e' := (1 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq3 := pr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have c3 := fsapprox_const 0xBFA48228B5688F3B (by decide +kernel) (((401 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb3 : |value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)| ≤ (401 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 80) (1 / 20) (401 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a3 := (fsapprox_add c3 pq3 (401 / 10000) hb3 (by norm_num)).mono
    (M' := (401 / 10000)) (e' := (403 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr2 := (fsapprox_mul tk a3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (401 / 200000)) (e' := (41 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq2 := pr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have c2 := fsapprox_const 0x3FC9C1550E884455 (by decide +kernel) (((2013 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb2 : |value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))| ≤ (251 / 1250) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 80) (1 / 20) (251 / 1250) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a2 := (fsapprox_add c2 pq2 (251 / 1250) hb2 (by norm_num)).mono
    (M' := (251 / 1250)) (e' := (41 / 200) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr1 := (fsapprox_mul tk a2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (101 / 10000)) (e' := (203 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq1 := pr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have c1 := fsapprox_const 0xBFD4D61203EB6F7D (by decide +kernel) (((407 / 1250) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb1 : |value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)))| ≤ (3231 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 80) (1 / 20) (3231 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a1 := (fsapprox_add c1 pq1 (3231 / 10000) hb1 (by norm_num)).mono
    (M' := (3231 / 10000)) (e' := (687 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr0 := (fsapprox_mul tk a1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (81 / 5000)) (e' := (167 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq0 := pr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have c0 := fsapprox_const 0x3FC5555555555555 (by decide +kernel) (((1667 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb0 : |value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))| ≤ (1627 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC5555555555555, ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] (1 / 80) (1 / 20) (1627 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a0 := (fsapprox_add c0 pq0 (1627 / 10000) hb0 (by norm_num)).mono
    (M' := (1627 / 10000)) (e' := (981 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p0 := (fsapprox_mul ht a0 (1 / 2 ^ 960) hησ' (by norm_num)).mono
    (M' := (1627 / 10000)) (e' := (359 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p1 := p0.rescale σ 1 hσp hσ1 (by rw [mul_one, one_mul])
  have d4 := fsapprox_const 0x3FB3B8C5B12E9282 (by decide +kernel) (((771 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have qr3 := (fsapprox_mul tk d4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (771 / 200000)) (e' := (39 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq3 := qr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have d3c := fsapprox_const 0xBFE6066C1B8D0159 (by decide +kernel) (((6883 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq3 : |value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282| ≤ (3437 / 5000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 80) (1 / 20) (3437 / 5000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d3 := (fsapprox_add d3c qq3 (3437 / 5000) hq3 (by norm_num)).mono
    (M' := (3437 / 5000)) (e' := (3457 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr2 := (fsapprox_mul tk d3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (43 / 1250)) (e' := (69 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq2 := qr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have d2c := fsapprox_const 0x40002AE59C598AC8 (by decide +kernel) (((2021 / 1000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq2 : |value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)| ≤ (5031 / 2500) * 1 := by
    have h := poly_bound [ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 80) (1 / 20) (5031 / 2500) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d2 := (fsapprox_add d2c qq2 (5031 / 2500) hq2 (by norm_num)).mono
    (M' := (5031 / 2500)) (e' := (4163 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr1 := (fsapprox_mul tk d2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (1007 / 10000)) (e' := (2047 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq1 := qr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have d1c := fsapprox_const 0xC0033A271C8A2D4B (by decide +kernel) (((12017 / 5000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq1 : |value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))| ≤ (2973 / 1250) * 1 := by
    have h := poly_bound [ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 80) (1 / 20) (2973 / 1250) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d1 := (fsapprox_add d1c qq1 (2973 / 1250) hq1 (by norm_num)).mono
    (M' := (2973 / 1250)) (e' := (3229 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr0 := (fsapprox_mul tk d1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (119 / 1000)) (e' := (2481 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq0 := qr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have hq0 : |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| ≤ (1213 / 1250) * 1 := by
    have h := poly_bound [1, ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 80) (1 / 20) (1213 / 1250) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have q0 := (fsapprox_add one1 qq0 (1213 / 1250) hq0 (by norm_num)).mono
    (M' := (1213 / 1250)) (e' := (6093 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hmq : (88471 / 100000) ≤ |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| := by
    have h := poly_bound [(36233 / 500000), ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] (1 / 80) (1 / 20) (5353 / 125000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    push_cast at h
    have h2 := (abs_le.mp h).1
    rw [abs_of_pos (by norm_num at h2 ⊢; linarith)]
    norm_num at h2 ⊢; linarith
  have r0 := (fsapprox_div p1 q0 (88471 / 100000) hmq (by norm_num) (1 / 2 ^ 960) hησ (by norm_num)).mono
    (M' := (23 / 125)) (e' := (843 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  exact r0

theorem ratio_A4 (t : Float) (vt σ : ℝ) (ht : FSApprox t vt σ 1 (0 / 2 ^ 53))
    (hlo : 0 ≤ vt) (hhi : vt ≤ (1 / 79)) (hσ : σ ≤ (1 / 79)) (hσ0 : 1 / 2 ^ 56 ≤ σ) :
    FSApprox (Asin.asinRatio t) (vt * (value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))) / (1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))))) σ (1719 / 10000)
      ((891 / 1250) / 2 ^ 53) := by
  have hσp : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hσ1 : σ ≤ 1 := hσ.trans (by norm_num)
  have hk1 : σ ≤ (1 / 79) * 1 := by rw [mul_one]; exact hσ
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hησ : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * σ := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 56) ≤ 1 / 2 ^ 960 * σ :=
      mul_le_mul_of_nonneg_left hσ0 (by positivity)
    norm_num at this ⊢
    linarith
  have hησ' : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * 1) := by rw [mul_one]; exact hησ
  have one1 := one_sapprox
  have tk := (ht.rescale 1 (1 / 79) one_pos le_rfl hk1).mono
    (M' := (127 / 10000)) (e' := 0 / 2 ^ 53) (by norm_num) (by norm_num)
  have c5 := fsapprox_const 0x3F023DE10DFDF709 (by decide +kernel) (((87 / 2500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have pr4 := (fsapprox_mul tk c5 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (9 / 20000000)) (e' := (1 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq4 := pr4.rescale 1 1 one_pos le_rfl (by norm_num)
  have c4 := fsapprox_const 0x3F49EFE07501B288 (by decide +kernel) (((39577 / 50000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb4 : |value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709| ≤ (9901 / 12500000) * 1 := by
    have h := poly_bound [ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 79) (9901 / 12500000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a4 := (fsapprox_add c4 pq4 (9901 / 12500000) hb4 (by norm_num)).mono
    (M' := (9901 / 12500000)) (e' := (9 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr3 := (fsapprox_mul tk a4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (503 / 50000000)) (e' := (1 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq3 := pr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have c3 := fsapprox_const 0xBFA48228B5688F3B (by decide +kernel) (((401 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb3 : |value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)| ≤ (401 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 79) (401 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a3 := (fsapprox_add c3 pq3 (401 / 10000) hb3 (by norm_num)).mono
    (M' := (401 / 10000)) (e' := (403 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr2 := (fsapprox_mul tk a3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (50927 / 100000000)) (e' := (11 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq2 := pr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have c2 := fsapprox_const 0x3FC9C1550E884455 (by decide +kernel) (((2013 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb2 : |value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))| ≤ (2013 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 79) (2013 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a2 := (fsapprox_add c2 pq2 (2013 / 10000) hb2 (by norm_num)).mono
    (M' := (2013 / 10000)) (e' := (81 / 400) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr1 := (fsapprox_mul tk a2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (255651 / 100000000)) (e' := (13 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq1 := pr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have c1 := fsapprox_const 0xBFD4D61203EB6F7D (by decide +kernel) (((407 / 1250) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb1 : |value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)))| ≤ (407 / 1250) * 1 := by
    have h := poly_bound [ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 79) (407 / 1250) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a1 := (fsapprox_add c1 pq1 (407 / 1250) hb1 (by norm_num)).mono
    (M' := (407 / 1250)) (e' := (3309 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr0 := (fsapprox_mul tk a1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (51689 / 12500000)) (e' := (21 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq0 := pr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have c0 := fsapprox_const 0x3FC5555555555555 (by decide +kernel) (((1667 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb0 : |value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))| ≤ (1667 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC5555555555555, ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 79) (1667 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a0 := (fsapprox_add c0 pq0 (1667 / 10000) hb0 (by norm_num)).mono
    (M' := (1667 / 10000)) (e' := (219 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have p0 := (fsapprox_mul ht a0 (1 / 2 ^ 960) hησ' (by norm_num)).mono
    (M' := (1667 / 10000)) (e' := (171 / 500) / 2 ^ 53) (by norm_num) (by norm_num)
  have p1 := p0.rescale σ 1 hσp hσ1 (by rw [mul_one, one_mul])
  have d4 := fsapprox_const 0x3FB3B8C5B12E9282 (by decide +kernel) (((771 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have qr3 := (fsapprox_mul tk d4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (97917 / 100000000)) (e' := (1 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq3 := qr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have d3c := fsapprox_const 0xBFE6066C1B8D0159 (by decide +kernel) (((6883 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq3 : |value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282| ≤ (6883 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 79) (6883 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d3 := (fsapprox_add d3c qq3 (6883 / 10000) hq3 (by norm_num)).mono
    (M' := (6883 / 10000)) (e' := (3447 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr2 := (fsapprox_mul tk d3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (874141 / 100000000)) (e' := (7 / 400) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq2 := qr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have d2c := fsapprox_const 0x40002AE59C598AC8 (by decide +kernel) (((2021 / 1000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq2 : |value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)| ≤ (2021 / 1000) * 1 := by
    have h := poly_bound [ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 79) (2021 / 1000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d2 := (fsapprox_add d2c qq2 (2021 / 1000) hq2 (by norm_num)).mono
    (M' := (2021 / 1000)) (e' := (10193 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr1 := (fsapprox_mul tk d2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (257 / 10000)) (e' := (129 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq1 := qr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have d1c := fsapprox_const 0xC0033A271C8A2D4B (by decide +kernel) (((12017 / 5000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq1 : |value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))| ≤ (4807 / 2000) * 1 := by
    have h := poly_bound [ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 79) (4807 / 2000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d1 := (fsapprox_add d1c qq1 (4807 / 2000) hq1 (by norm_num)).mono
    (M' := (4807 / 2000)) (e' := (3069 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr0 := (fsapprox_mul tk d1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (153 / 5000)) (e' := (309 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq0 := qr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have hq0 : |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| ≤ (10001 / 10000) * 1 := by
    have h := poly_bound [1, ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 79) (10001 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have q0 := (fsapprox_add one1 qq0 (10001 / 10000) hq0 (by norm_num)).mono
    (M' := (10001 / 10000)) (e' := (531 / 500) / 2 ^ 53) (by norm_num) (by norm_num)
  have hmq : (969867 / 1000000) ≤ |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| := by
    have h := poly_bound [(15051 / 1000000), ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 79) (7541 / 500000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    push_cast at h
    have h2 := (abs_le.mp h).1
    rw [abs_of_pos (by norm_num at h2 ⊢; linarith)]
    norm_num at h2 ⊢; linarith
  have r0 := (fsapprox_div p1 q0 (969867 / 1000000) hmq (by norm_num) (1 / 2 ^ 960) hησ (by norm_num)).mono
    (M' := (1719 / 10000)) (e' := (891 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  exact r0

theorem ratio_W (t : Float) (vt σ : ℝ) (ht : FSApprox t vt σ 1 (0 / 2 ^ 53))
    (hlo : 0 ≤ vt) (hhi : vt ≤ (1 / 4)) (hσ : σ ≤ (1 / 4)) (hσ0 : 1 / 2 ^ 56 ≤ σ) :
    FSApprox (Asin.asinRatio t) (vt * (value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))) / (1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))))) σ (1621 / 5000)
      ((29019 / 10000) / 2 ^ 53) := by
  have hσp : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hσ1 : σ ≤ 1 := hσ.trans (by norm_num)
  have hk1 : σ ≤ (1 / 4) * 1 := by rw [mul_one]; exact hσ
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hησ : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * σ := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ 56) ≤ 1 / 2 ^ 960 * σ :=
      mul_le_mul_of_nonneg_left hσ0 (by positivity)
    norm_num at this ⊢
    linarith
  have hησ' : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * 1) := by rw [mul_one]; exact hησ
  have one1 := one_sapprox
  have tk := (ht.rescale 1 (1 / 4) one_pos le_rfl hk1).mono
    (M' := (1 / 4)) (e' := 0 / 2 ^ 53) (by norm_num) (by norm_num)
  have c5 := fsapprox_const 0x3F023DE10DFDF709 (by decide +kernel) (((87 / 2500000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have pr4 := (fsapprox_mul tk c5 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (87 / 10000000)) (e' := (1 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq4 := pr4.rescale 1 1 one_pos le_rfl (by norm_num)
  have c4 := fsapprox_const 0x3F49EFE07501B288 (by decide +kernel) (((39577 / 50000000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb4 : |value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709| ≤ (16007 / 20000000) * 1 := by
    have h := poly_bound [ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 4) (16007 / 20000000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a4 := (fsapprox_add c4 pq4 (16007 / 20000000) hb4 (by norm_num)).mono
    (M' := (16007 / 20000000)) (e' := (1 / 1000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr3 := (fsapprox_mul tk a4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (20009 / 100000000)) (e' := (1 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq3 := pr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have c3 := fsapprox_const 0xBFA48228B5688F3B (by decide +kernel) (((401 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb3 : |value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)| ≤ (401 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 4) (401 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a3 := (fsapprox_add c3 pq3 (401 / 10000) hb3 (by norm_num)).mono
    (M' := (401 / 10000)) (e' := (407 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr2 := (fsapprox_mul tk a3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (101 / 10000)) (e' := (203 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq2 := pr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have c2 := fsapprox_const 0x3FC9C1550E884455 (by decide +kernel) (((2013 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb2 : |value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))| ≤ (2013 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 4) (2013 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a2 := (fsapprox_add c2 pq2 (2013 / 10000) hb2 (by norm_num)).mono
    (M' := (2013 / 10000)) (e' := (2217 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr1 := (fsapprox_mul tk a2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (63 / 1250)) (e' := (529 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq1 := pr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have c1 := fsapprox_const 0xBFD4D61203EB6F7D (by decide +kernel) (((407 / 1250) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb1 : |value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709)))| ≤ (3257 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 4) (3257 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a1 := (fsapprox_add c1 pq1 (3257 / 10000) hb1 (by norm_num)).mono
    (M' := (3257 / 10000)) (e' := (1079 / 2500) / 2 ^ 53) (by norm_num) (by norm_num)
  have pr0 := (fsapprox_mul tk a1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (163 / 2000)) (e' := (947 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have pq0 := pr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have c0 := fsapprox_const 0x3FC5555555555555 (by decide +kernel) (((1667 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hb0 : |value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt * (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt * (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))| ≤ (417 / 2500) * 1 := by
    have h := poly_bound [ratOfWord 0x3FC5555555555555, ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455, ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709] 0 (1 / 4) (417 / 2500) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have a0 := (fsapprox_add c0 pq0 (417 / 2500) hb0 (by norm_num)).mono
    (M' := (417 / 2500)) (e' := (3563 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have p0 := (fsapprox_mul ht a0 (1 / 2 ^ 960) hησ' (by norm_num)).mono
    (M' := (417 / 2500)) (e' := (327 / 625) / 2 ^ 53) (by norm_num) (by norm_num)
  have p1 := p0.rescale σ 1 hσp hσ1 (by rw [mul_one, one_mul])
  have d4 := fsapprox_const 0x3FB3B8C5B12E9282 (by decide +kernel) (((771 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have qr3 := (fsapprox_mul tk d4 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (193 / 10000)) (e' := (193 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq3 := qr3.rescale 1 1 one_pos le_rfl (by norm_num)
  have d3c := fsapprox_const 0xBFE6066C1B8D0159 (by decide +kernel) (((6883 / 10000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq3 : |value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282| ≤ (1721 / 2500) * 1 := by
    have h := poly_bound [ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 4) (1721 / 2500) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d3 := (fsapprox_add d3c qq3 (1721 / 2500) hq3 (by norm_num)).mono
    (M' := (1721 / 2500)) (e' := (3539 / 5000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr2 := (fsapprox_mul tk d3 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (1721 / 10000)) (e' := (3491 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq2 := qr2.rescale 1 1 one_pos le_rfl (by norm_num)
  have d2c := fsapprox_const 0x40002AE59C598AC8 (by decide +kernel) (((2021 / 1000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq2 : |value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)| ≤ (5053 / 2500) * 1 := by
    have h := poly_bound [ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 4) (5053 / 2500) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d2 := (fsapprox_add d2c qq2 (5053 / 2500) hq2 (by norm_num)).mono
    (M' := (5053 / 2500)) (e' := (2963 / 1250) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr1 := (fsapprox_mul tk d2 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (5053 / 10000)) (e' := (549 / 500) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq1 := qr1.rescale 1 1 one_pos le_rfl (by norm_num)
  have d1c := fsapprox_const 0xC0033A271C8A2D4B (by decide +kernel) (((12017 / 5000) : ℚ) : ℝ)
    (abs_value_le _ _ (by decide +kernel))
  have hq1 : |value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282))| ≤ (24039 / 10000) * 1 := by
    have h := poly_bound [ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 4) (24039 / 10000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have d1 := (fsapprox_add d1c qq1 (24039 / 10000) hq1 (by norm_num)).mono
    (M' := (24039 / 10000)) (e' := (1751 / 500) / 2 ^ 53) (by norm_num) (by norm_num)
  have qr0 := (fsapprox_mul tk d1 (1 / 2 ^ 960) hη1 (by norm_num)).mono
    (M' := (601 / 1000)) (e' := (2953 / 2000) / 2 ^ 53) (by norm_num) (by norm_num)
  have qq0 := qr0.rescale 1 1 one_pos le_rfl (by norm_num)
  have hq0 : |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| ≤ (2001 / 2000) * 1 := by
    have h := poly_bound [1, ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 4) (2001 / 2000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    rw [mul_one]; push_cast at h; exact h
  have q0 := (fsapprox_add one1 qq0 (2001 / 2000) hq0 (by norm_num)).mono
    (M' := (2001 / 2000)) (e' := (24771 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hmq : (12863 / 25000) ≤ |1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt * (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))| := by
    have h := poly_bound [(242497 / 1000000), ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159, ratOfWord 0x3FB3B8C5B12E9282] 0 (1 / 4) (242983 / 1000000) 12 (by decide +kernel) vt
      (by push_cast; linarith) (by push_cast; linarith)
    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h
    push_cast at h
    have h2 := (abs_le.mp h).1
    rw [abs_of_pos (by norm_num at h2 ⊢; linarith)]
    norm_num at h2 ⊢; linarith
  have r0 := (fsapprox_div p1 q0 (12863 / 25000) hmq (by norm_num) (1 / 2 ^ 960) hησ (by norm_num)).mono
    (M' := (1621 / 5000)) (e' := (29019 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  exact r0

end Verified.Examples.AsinTheoremRatio
