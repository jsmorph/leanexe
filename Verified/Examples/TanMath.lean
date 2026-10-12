import Verified.Examples.TanPoly
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Real facts for the tangent kernel: the cosine stays above `0.76` on `|x| ≤ 0.6745`, so `tan`
is `1/0.76 ^ 2`-Lipschitz there, and `tan (a + b)` with a tail `b ≤ |a| / 2 ^ 52` differs from
the kernel's `a P (a ^ 2) + b (1 + a ^ 2)` by the polynomial's error, `|b| (tan ^ 2 a - a ^ 2)`,
and a term in `b ^ 2`.
-/

namespace Verified.Examples.TanMath

open CodeLib.IEEE64 LeanExe.ProofKit PolyBound TrigApprox TanWords TanPoly

theorem cos_lower (a : ℝ) (ha : |a| ≤ 6745 / 10000) : 76 / 100 ≤ Real.cos a := by
  have ha1 : |a| ≤ 1 := ha.trans (by norm_num)
  have hcb := Real.cos_bound ha1
  have h2 : a ^ 2 ≤ (6745 / 10000) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have h4 : |a| ^ 4 ≤ (6745 / 10000) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) ha 4
  have := (abs_le.mp hcb).1
  nlinarith

/-- `tan` changes by at most `|a - b| / 0.76 ^ 2` on `|x| ≤ 0.6745`. -/
theorem tan_diff (a b : ℝ) (ha : |a| ≤ 6745 / 10000) (hb : |b| ≤ 6745 / 10000) :
    |Real.tan a - Real.tan b| ≤ |a - b| / (76 / 100) ^ 2 := by
  have hca := cos_lower a ha
  have hcb := cos_lower b hb
  have hid : Real.tan a - Real.tan b = Real.sin (a - b) / (Real.cos a * Real.cos b) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.sin_sub]
    field_simp
  have hs : |Real.sin (a - b)| ≤ |a - b| := by
    have := Real.abs_sin_sub_sin_le (a - b) 0
    simpa using this
  rw [hid, abs_div, abs_of_pos (by positivity : 0 < Real.cos a * Real.cos b)]
  have hcc : (76 / 100 : ℝ) ^ 2 ≤ Real.cos a * Real.cos b := by nlinarith
  calc |Real.sin (a - b)| / (Real.cos a * Real.cos b) ≤ |a - b| / (Real.cos a * Real.cos b) :=
        div_le_div_of_nonneg_right hs (by positivity)
    _ ≤ |a - b| / (76 / 100) ^ 2 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hcc

/-- The kernel polynomial's coefficients bound `polyT`. -/
theorem polyT_bound (Z : ℝ) (h0 : 0 ≤ Z) (h1 : Z ≤ 455 / 1000) : |polyT Z| ≤ 1636 / 10000 := by
  obtain ⟨-, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := coeffs_AB
  have m1 := c1.2; have m2 := c2.2; have m3 := c3.2; have m4 := c4.2; have m5 := c5.2
  have m6 := c6.2; have m7 := c7.2; have m8 := c8.2; have m9 := c9.2; have m10 := c10.2
  have m11 := c11.2; have m12 := c12.2
  have hW0 : 0 ≤ Z * Z := mul_nonneg h0 h0
  have hW1 : Z * Z ≤ 2071 / 10000 := by nlinarith
  have step : ∀ (c t : ℝ) (mc mt : ℝ), |c| ≤ mc → |t| ≤ mt → |c + Z * Z * t| ≤ mc + 2071 / 10000 * mt := by
    intro c t mc mt hc ht
    calc |c + Z * Z * t| ≤ |c| + |Z * Z * t| := abs_add_le _ _
      _ ≤ mc + 2071 / 10000 * mt := by
        rw [abs_mul, abs_of_nonneg hW0]
        exact add_le_add hc (mul_le_mul hW1 ht (abs_nonneg _) (by norm_num))
  have s9 := step _ _ _ _ m9 m11
  have s7 := step _ _ _ _ m7 s9
  have s5 := step _ _ _ _ m5 s7
  have s3 := step _ _ _ _ m3 s5
  have s1 := step _ _ _ _ m1 s3
  have t10 := step _ _ _ _ m10 m12
  have t8 := step _ _ _ _ m8 t10
  have t6 := step _ _ _ _ m6 t8
  have t4 := step _ _ _ _ m4 t6
  have t2 := step _ _ _ _ m2 t4
  unfold polyT
  calc _ ≤ |value wT1 + Z * Z * (value wT3 + Z * Z * (value wT5 + Z * Z * (value wT7 + Z * Z *
        (value wT9 + Z * Z * value wT11))))| +
      |Z * (value wT2 + Z * Z * (value wT4 + Z * Z * (value wT6 + Z * Z * (value wT8 + Z * Z *
        (value wT10 + Z * Z * value wT12)))))| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg h0]
      have := mul_le_mul h1 t2 (abs_nonneg _) (by norm_num)
      norm_num at s1 this ⊢
      linarith

/-- `|sin b - b cos b| ≤ b ^ 2` for small `b`. -/
theorem sin_sub_mul_cos (b : ℝ) (hb : |b| ≤ 1 / 2 ^ 40) : |Real.sin b - b * Real.cos b| ≤ b ^ 2 := by
  have hb1 : |b| ≤ 1 := hb.trans (by norm_num)
  have hsb := Real.sin_bound hb1
  have hcb := Real.cos_bound hb1
  have hb0 := abs_nonneg b
  have hbsq : |b| ^ 2 = b ^ 2 := sq_abs b
  have hq : |b| ≤ 1 / 4 := hb.trans (by norm_num)
  have hb3 : |b| ^ 3 ≤ b ^ 2 / 4 := by
    rw [← hbsq, show |b| ^ 3 = |b| * |b| ^ 2 by ring, show |b| ^ 2 / 4 = 1 / 4 * |b| ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hq (by positivity)
  have hb2 : |b| ^ 2 ≤ 1 / 4 := by
    rw [show |b| ^ 2 = |b| * |b| by ring]
    exact (mul_le_mul hq hq hb0 (by norm_num)).trans (by norm_num)
  have hb5 : |b| ^ 5 ≤ b ^ 2 / 4 := by
    rw [← hbsq, show |b| ^ 5 = |b| ^ 3 * |b| ^ 2 by ring, show |b| ^ 2 / 4 = 1 / 4 * |b| ^ 2 by ring]
    have : |b| ^ 3 ≤ 1 / 4 := hb3.trans (by rw [← hbsq]; linarith)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h3 : |b * (Real.cos b - (1 - b ^ 2 / 2))| ≤ b ^ 2 / 4 * (5 / 96) := by
    rw [abs_mul]
    calc |b| * |Real.cos b - (1 - b ^ 2 / 2)| ≤ |b| * (|b| ^ 4 * (5 / 96)) :=
          mul_le_mul_of_nonneg_left hcb hb0
      _ = |b| ^ 5 * (5 / 96) := by ring
      _ ≤ b ^ 2 / 4 * (5 / 96) := mul_le_mul_of_nonneg_right hb5 (by norm_num)
  have hb3' : |b ^ 3| ≤ b ^ 2 / 4 := by rw [abs_pow]; exact hb3
  have e1 := abs_le.mp hsb
  have e3 := abs_le.mp h3
  have e4 := abs_le.mp hb3'
  rw [abs_le]
  constructor <;> nlinarith

/-- The second-order term of `tan (a + b)`. -/
theorem tan_second (a b : ℝ) (hca : 76 / 100 ≤ Real.cos a) (hcab : 76 / 100 ≤ Real.cos (a + b))
    (hb : |b| ≤ 1 / 2 ^ 40) :
    |Real.tan (a + b) - Real.tan a - b * (1 + Real.tan a ^ 2)| ≤ 5 * b ^ 2 := by
  have hca0 : Real.cos a ≠ 0 := by linarith
  have hcab0 : Real.cos (a + b) ≠ 0 := by linarith
  have hs : Real.sin b = Real.sin (a + b) * Real.cos a - Real.cos (a + b) * Real.sin a := by
    rw [← Real.sin_sub]
    ring_nf
  have hd1 : Real.tan (a + b) - Real.tan a = Real.sin b / (Real.cos (a + b) * Real.cos a) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, div_sub_div _ _ hcab0 hca0, hs]
  have hd2 : 1 + Real.tan a ^ 2 = 1 / Real.cos a ^ 2 := by
    have := Real.sin_sq_add_cos_sq a
    rw [Real.tan_eq_sin_div_cos, div_pow, eq_div_iff (pow_ne_zero 2 hca0), add_mul,
      div_mul_cancel₀ _ (pow_ne_zero 2 hca0)]
    linarith
  have hN : Real.tan (a + b) - Real.tan a - b * (1 + Real.tan a ^ 2) =
      (Real.sin b * Real.cos a - b * Real.cos (a + b)) / (Real.cos (a + b) * Real.cos a ^ 2) := by
    rw [hd1, hd2]
    field_simp
  have hN' : Real.sin b * Real.cos a - b * Real.cos (a + b) =
      Real.cos a * (Real.sin b - b * Real.cos b) + b * Real.sin a * Real.sin b := by
    rw [Real.cos_add]
    ring
  have hsb' : |Real.sin b| ≤ |b| := by
    have := Real.abs_sin_sub_sin_le b 0
    simpa using this
  have hb0 := abs_nonneg b
  have hNb : |Real.sin b * Real.cos a - b * Real.cos (a + b)| ≤ 2 * b ^ 2 := by
    rw [hN']
    have e1 : |Real.cos a * (Real.sin b - b * Real.cos b)| ≤ b ^ 2 := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one a)).trans
        (sin_sub_mul_cos b hb)
    have e2 : |b * Real.sin a * Real.sin b| ≤ b ^ 2 := by
      rw [abs_mul, abs_mul, ← sq_abs b, sq]
      exact mul_le_mul (mul_le_of_le_one_right hb0 (Real.abs_sin_le_one a)) hsb'
        (abs_nonneg _) hb0
    exact (abs_add_le _ _).trans (by linarith)
  have hden : (76 / 100 : ℝ) ^ 3 ≤ Real.cos (a + b) * Real.cos a ^ 2 := by
    have h2 : (76 / 100 : ℝ) ^ 2 ≤ Real.cos a ^ 2 := pow_le_pow_left₀ (by norm_num) hca 2
    calc (76 / 100 : ℝ) ^ 3 = 76 / 100 * (76 / 100) ^ 2 := by ring
      _ ≤ Real.cos (a + b) * Real.cos a ^ 2 := mul_le_mul hcab h2 (by norm_num) (by linarith)
  have hpos : 0 < Real.cos (a + b) * Real.cos a ^ 2 :=
    mul_pos (by linarith) (pow_pos (by linarith) 2)
  rw [hN, abs_div, abs_of_pos hpos]
  calc _ ≤ 2 * b ^ 2 / (Real.cos (a + b) * Real.cos a ^ 2) :=
        div_le_div_of_nonneg_right hNb (by positivity)
    _ ≤ 2 * b ^ 2 / (76 / 100) ^ 3 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ ≤ 5 * b ^ 2 := by
        rw [div_le_iff₀ (by norm_num)]
        nlinarith [sq_nonneg b]

set_option maxHeartbeats 1000000 in
/-- `|tan a - a P (a ^ 2) - b (1 + a ^ 2)|` for a tail `|b| ≤ |a| / 2 ^ 52`. -/
theorem tan_tail_expand (a b : ℝ) (ha : |a| ≤ 67434 / 100000) (hb : |b| ≤ |a| / 2 ^ 52) :
    |Real.tan (a + b) - (a * eval TanKernelPoly.tanKernel (a ^ 2) + b * (1 + a ^ 2))| ≤
      |a| * ((59 / 64) / 2 ^ 59) + |b| * (9 / 10 * |a| ^ 4 + |a| ^ 2 / 2 ^ 57) + 5 * b ^ 2 := by
  have hk := TanKernelPoly.tan_kernel_error a ha
  have hb40 : |b| ≤ 1 / 2 ^ 40 := hb.trans (by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith)
  have hab : |a + b| ≤ 6745 / 10000 := (abs_add_le _ _).trans (by linarith)
  have hD := tan_second a b (cos_lower a (by linarith)) (cos_lower (a + b) hab) hb40
  set A := |a| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  have hA2 : A ^ 2 ≤ 4548 / 10000 := by
    have := pow_le_pow_left₀ hA0 ha 2
    linarith [show ((67434 : ℝ) / 100000) ^ 2 ≤ 4548 / 10000 by norm_num]
  have haa : a * a = A ^ 2 := by rw [hA, sq_abs, sq]
  have hP : a * eval TanKernelPoly.tanKernel (a ^ 2) - a = corrT a 0 := by
    have := corrT_eval a 0
    linarith
  have hpT := polyT_bound (a * a) (mul_self_nonneg a) (by rw [haa]; linarith)
  have hT0 := (coeffs_AB.1).2
  have hc : |corrT a 0| ≤ 3334 / 10000 * A ^ 3 + 1636 / 10000 * A ^ 5 := by
    unfold corrT
    simp only [zero_add, add_zero]
    have h1 : |a * a * (a * a * a * polyT (a * a))| ≤ A ^ 5 * (1636 / 10000) := by
      rw [show a * a * (a * a * a * polyT (a * a)) = a ^ 5 * polyT (a * a) by ring, abs_mul,
        abs_pow]
      exact mul_le_mul_of_nonneg_left hpT (by positivity)
    have h2 : |value wT0 * (a * a * a)| ≤ 3334 / 10000 * A ^ 3 := by
      rw [show a * a * a = a ^ 3 by ring, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_right hT0 (by positivity)
    calc _ ≤ |a * a * (a * a * a * polyT (a * a))| + |value wT0 * (a * a * a)| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hA5 : A ^ 5 ≤ 4548 / 10000 * A ^ 3 := by
    rw [show A ^ 5 = A ^ 2 * A ^ 3 by ring]
    exact mul_le_mul_of_nonneg_right hA2 (by positivity)
  have hA3 : A ^ 3 ≤ 4548 / 10000 * A := by
    rw [show A ^ 3 = A ^ 2 * A by ring]
    exact mul_le_mul_of_nonneg_right hA2 hA0
  have htm : |Real.tan a - a| ≤ 4079 / 10000 * A ^ 3 + A * ((59 / 64) / 2 ^ 59) := by
    have h := abs_sub_le (Real.tan a) (a * eval TanKernelPoly.tanKernel (a ^ 2)) a
    rw [hP] at h
    have : 0 ≤ A ^ 3 := pow_nonneg hA0 3
    linarith [hk, hc, hA5]
  have htp : |Real.tan a + a| ≤ 22 / 10 * A := by
    have h := abs_add_le (Real.tan a - a) (2 * a)
    rw [show Real.tan a - a + 2 * a = Real.tan a + a by ring, abs_mul, abs_two] at h
    have : A * ((59 / 64) / 2 ^ 59) ≤ A / 100 := by
      have : (59 / 64 : ℝ) / 2 ^ 59 ≤ 1 / 100 := by norm_num
      nlinarith
    linarith
  have hsq : |Real.tan a ^ 2 - a ^ 2| ≤ 9 / 10 * A ^ 4 + A ^ 2 / 2 ^ 57 := by
    rw [show Real.tan a ^ 2 - a ^ 2 = (Real.tan a - a) * (Real.tan a + a) by ring, abs_mul]
    have hm := mul_le_mul htm htp (abs_nonneg _) (by positivity)
    have e1 : 4079 / 10000 * A ^ 3 * (22 / 10 * A) ≤ 9 / 10 * A ^ 4 := by
      have : 0 ≤ A ^ 4 := by positivity
      rw [show 4079 / 10000 * A ^ 3 * (22 / 10 * A) = 4079 / 10000 * (22 / 10) * A ^ 4 by ring]
      nlinarith
    have e2 : A * ((59 / 64) / 2 ^ 59) * (22 / 10 * A) ≤ A ^ 2 / 2 ^ 57 := by
      have : (59 / 64 : ℝ) / 2 ^ 59 * (22 / 10) ≤ 1 / 2 ^ 57 := by norm_num
      have h2 : 0 ≤ A ^ 2 := by positivity
      rw [show A * ((59 / 64) / 2 ^ 59) * (22 / 10 * A) = (59 / 64 / 2 ^ 59 * (22 / 10)) * A ^ 2 by
        ring, show A ^ 2 / 2 ^ 57 = 1 / 2 ^ 57 * A ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right this h2
    have : (4079 / 10000 * A ^ 3 + A * ((59 / 64) / 2 ^ 59)) * (22 / 10 * A) =
        4079 / 10000 * A ^ 3 * (22 / 10 * A) + A * ((59 / 64) / 2 ^ 59) * (22 / 10 * A) := by ring
    linarith
  have hid : Real.tan (a + b) - (a * eval TanKernelPoly.tanKernel (a ^ 2) + b * (1 + a ^ 2)) =
      (Real.tan a - a * eval TanKernelPoly.tanKernel (a ^ 2)) +
        (Real.tan (a + b) - Real.tan a - b * (1 + Real.tan a ^ 2)) +
        b * (Real.tan a ^ 2 - a ^ 2) := by ring
  rw [hid]
  have hb2 : |b * (Real.tan a ^ 2 - a ^ 2)| ≤ |b| * (9 / 10 * A ^ 4 + A ^ 2 / 2 ^ 57) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
  calc _ ≤ |Real.tan a - a * eval TanKernelPoly.tanKernel (a ^ 2)| +
        |Real.tan (a + b) - Real.tan a - b * (1 + Real.tan a ^ 2)| +
        |b * (Real.tan a ^ 2 - a ^ 2)| := by
          refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

#print axioms cos_lower
#print axioms tan_diff
#print axioms polyT_bound
#print axioms sin_sub_mul_cos
#print axioms tan_second
#print axioms tan_tail_expand

end Verified.Examples.TanMath
