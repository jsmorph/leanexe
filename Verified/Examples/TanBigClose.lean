import Verified.Examples.TanEven

/-!
The real error of `Tan.kernelTan` from `0x3FE59428` on.  With `T_v (y) = v - 2 y v/(y + v)`,
`T_1 (tan b) = tan (π/4 - b)` and `T_{-1} (tan b) = -1/tan (π/4 - b)`, and
`T_v (A) - T_v (B) = 2 (B - A)/((A + v) (B + v))`.  `big_close` bounds a real `τ` near
`T_v (W)`, with `W` near `tan a` and `a` near `b`, against `T_v (tan b)`: within `0.95 u` for
`|a| ≥ 0.05`, and within `0.45 u` with `|T_v (tan b)| ≥ 0.9` below.
-/

namespace Verified.Examples.TanBigClose

open CodeLib.IEEE64 LeanExe.ProofKit TanEven

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

set_option exponentiation.threshold 1200

theorem cos_small (a : ℝ) (ha : |a| ≤ 12 / 100) : 99 / 100 ≤ Real.cos a := by
  have hc := Real.cos_bound (x := a) (by linarith)
  have hc' := (abs_le.mp hc).1
  have h2 : a ^ 2 ≤ (12 / 100) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have h4 : |a| ^ 4 ≤ (12 / 100) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) ha 4
  norm_num at h2 h4
  linarith

theorem tan_diff_small (a b : ℝ) (ha : |a| ≤ 12 / 100) (hb : |b| ≤ 12 / 100) :
    |Real.tan a - Real.tan b| ≤ 10204 / 10000 * |a - b| := by
  have hca := cos_small a ha
  have hcb := cos_small b hb
  have hid : Real.tan a - Real.tan b = Real.sin (a - b) / (Real.cos a * Real.cos b) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.sin_sub]
    field_simp
  have hs : |Real.sin (a - b)| ≤ |a - b| := by
    have := Real.abs_sin_sub_sin_le (a - b) 0
    simpa using this
  have hcc : 99 / 100 * (99 / 100) ≤ Real.cos a * Real.cos b :=
    mul_le_mul hca hcb (by norm_num) (by linarith)
  rw [hid, abs_div, abs_of_pos (by linarith : 0 < Real.cos a * Real.cos b),
    div_le_iff₀ (by linarith)]
  have h1 : 10204 / 10000 * |a - b| * (99 / 100 * (99 / 100)) ≤
      10204 / 10000 * |a - b| * (Real.cos a * Real.cos b) :=
    mul_le_mul_of_nonneg_left hcc (by positivity)
  have h2 := abs_nonneg (a - b)
  linarith

theorem tan_small (a : ℝ) (ha : |a| ≤ 12 / 100) : |Real.tan a| ≤ 10204 / 10000 * |a| := by
  have h := tan_diff_small a 0 ha (by norm_num)
  rwa [Real.tan_zero, sub_zero, sub_zero] at h

/-- The final transformation of the kernel. -/
noncomputable def Tv (v y : ℝ) : ℝ := v - 2 * (y * v / (y + v))

theorem Tv_sub (v A B : ℝ) (hv : v = 1 ∨ v = -1) (hA : A + v ≠ 0) (hB : B + v ≠ 0) :
    Tv v A - Tv v B = 2 * (B - A) / ((A + v) * (B + v)) := by
  unfold Tv
  rcases hv with rfl | rfl <;> field_simp <;> ring

theorem near_one' (a v : ℝ) (hv : v = 1 ∨ v = -1) : 1 - |a| ≤ |a + v| := by
  have hv1 : |v| = 1 := by rcases hv with rfl | rfl <;> simp
  have h := abs_sub_abs_le_abs_sub v (-a)
  rw [sub_neg_eq_add, abs_neg, add_comm, hv1] at h
  exact h

theorem Tv_close (v A B m : ℝ) (hv : v = 1 ∨ v = -1) (hA : |A| ≤ m) (hB : |B| ≤ m)
    (hm : m < 1) : |Tv v A - Tv v B| ≤ 2 * |A - B| / ((1 - m) * (1 - m)) := by
  have hA1 := near_one' A v hv
  have hB1 := near_one' B v hv
  have hA0 : A + v ≠ 0 := fun h => by rw [h, abs_zero] at hA1; linarith
  have hB0 : B + v ≠ 0 := fun h => by rw [h, abs_zero] at hB1; linarith
  rw [Tv_sub v A B hv hA0 hB0, abs_div, abs_mul, abs_mul, abs_two, abs_sub_comm B A]
  have hD : (1 - m) * (1 - m) ≤ |A + v| * |B + v| :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (abs_nonneg _)
  exact div_le_div_of_nonneg_left (by positivity) (mul_pos (by linarith) (by linarith)) hD

theorem Tv_one (B : ℝ) (hB : B + 1 ≠ 0) : Tv 1 B = (1 - B) / (1 + B) := by
  unfold Tv
  rw [add_comm 1 B]
  field_simp
  ring

theorem Tv_negOne (B : ℝ) (hB : B - 1 ≠ 0) : Tv (-1) B = (1 + B) / (B - 1) := by
  unfold Tv
  rw [show B + -1 = B - 1 by ring]
  field_simp
  ring

/-- `tan (π/4 - b) = T_1 (tan b)` and `-1/tan (π/4 - b) = T_{-1} (tan b)` near 0. -/
theorem tan_quarter (b : ℝ) (hb : |b| ≤ 12 / 100) :
    Real.tan (Real.pi / 4 - b) = Tv 1 (Real.tan b) ∧
      -1 / Real.tan (Real.pi / 4 - b) = Tv (-1) (Real.tan b) := by
  have hc := cos_small b hb
  have ht := tan_small b hb
  have hs2 : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
  have hsin : Real.sin (Real.pi / 4 - b) = Real.sqrt 2 / 2 * (Real.cos b - Real.sin b) := by
    rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hcos : Real.cos (Real.pi / 4 - b) = Real.sqrt 2 / 2 * (Real.cos b + Real.sin b) := by
    rw [Real.cos_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have htb : Real.tan b = Real.sin b / Real.cos b := Real.tan_eq_sin_div_cos b
  have hsb : |Real.sin b| ≤ 12 / 100 := by
    have := Real.abs_sin_le_abs (x := b)
    linarith
  have hp : 0 < Real.cos b + Real.sin b := by
    have := (abs_le.mp hsb).1
    linarith
  have hn : 0 < Real.cos b - Real.sin b := by
    have := (abs_le.mp hsb).2
    linarith
  have hcb0 : Real.cos b ≠ 0 := ne_of_gt (by linarith)
  have hp0 : Real.cos b + Real.sin b ≠ 0 := ne_of_gt hp
  have hs0 : Real.sqrt 2 / 2 ≠ 0 := ne_of_gt hs2
  have hT : Real.tan (Real.pi / 4 - b) = (1 - Real.tan b) / (1 + Real.tan b) := by
    rw [Real.tan_eq_sin_div_cos, hsin, hcos, htb]
    have h1 : 1 + Real.sin b / Real.cos b = (Real.cos b + Real.sin b) / Real.cos b := by
      rw [eq_div_iff hcb0, add_mul, div_mul_cancel₀ _ hcb0, one_mul]
    have h2 : 1 - Real.sin b / Real.cos b = (Real.cos b - Real.sin b) / Real.cos b := by
      rw [eq_div_iff hcb0, sub_mul, div_mul_cancel₀ _ hcb0, one_mul]
    rw [h1, h2, div_div_div_cancel_right₀ hcb0, mul_div_mul_left _ _ hs0]
  have htb1 : |Real.tan b| ≤ 1 / 5 := by
    have : 10204 / 10000 * |b| ≤ 10204 / 10000 * (12 / 100) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    linarith
  have hb1 : Real.tan b + 1 ≠ 0 := by
    have := (abs_le.mp htb1).1
    intro h; linarith
  have hb2 : Real.tan b - 1 ≠ 0 := by
    have := (abs_le.mp htb1).2
    intro h; linarith
  have hb3 : 1 - Real.tan b ≠ 0 := by
    intro h; apply hb2; linarith
  have hb4 : 1 + Real.tan b ≠ 0 := by
    intro h; apply hb1; linarith
  refine ⟨by rw [hT, Tv_one _ hb1], ?_⟩
  rw [hT, Tv_negOne _ hb2]
  field_simp
  ring

theorem even_err_lin (X : ℝ) (h0 : 0 ≤ X) (h1 : X ≤ 1113 / 10000) :
    even_err X ≤ 6 / 100 * 𝐮 * X + 9 * η := by
  have h2 : X ^ 2 ≤ (1113 / 10000) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : X ^ 3 ≤ (1113 / 10000) ^ 2 * X := by
    rw [show X ^ 3 = X ^ 2 * X by ring]
    exact mul_le_mul_of_nonneg_right h2 h0
  have h4 : X ^ 4 ≤ ((1113 / 10000) ^ 2) ^ 2 := by
    rw [show X ^ 4 = (X ^ 2) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have h5 : X ^ 5 ≤ ((1113 / 10000) ^ 2) ^ 2 * X := by
    rw [show X ^ 5 = X ^ 4 * X by ring]
    exact mul_le_mul_of_nonneg_right h4 h0
  unfold even_err
  rw [show 𝐮 = 1 / 2 ^ 53 from rfl]
  norm_num at h3 h5 ⊢
  linarith

/-- Bounds on `W`, `tan a`, and `tan b` for `|a| ≤ X`. -/
theorem three_small (W a b X E : ℝ) (hX : |a| = X) (hX1 : X ≤ 1113 / 10000)
    (hW : |W - Real.tan a| ≤ E) (hab : |a - b| ≤ 1001 / 1000 * 𝐮 * X + 1 / 2 ^ 59) :
    |Real.tan a| ≤ 10204 / 10000 * X ∧ |W| ≤ 10204 / 10000 * X + E ∧
      |Real.tan b| ≤ 10204 / 10000 * X + 1 / 2 ^ 55 ∧
      |Real.tan a - Real.tan b| ≤ 10204 / 10000 * (1001 / 1000 * 𝐮 * X + 1 / 2 ^ 59) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hX0 : 0 ≤ X := hX ▸ abs_nonneg _
  have ha : |a| ≤ 12 / 100 := by linarith
  have hb' : |b| ≤ X + (1001 / 1000 * 𝐮 * X + 1 / 2 ^ 59) := by
    have := abs_sub_abs_le_abs_sub b a
    rw [abs_sub_comm b a] at this
    linarith
  have hb : |b| ≤ 12 / 100 := by
    rw [hu] at hb'
    have : (1113 / 10000 : ℝ) + (1001 / 1000 * (1 / 2 ^ 53) * (1113 / 10000) + 1 / 2 ^ 59) ≤
        12 / 100 := by norm_num
    have : 1001 / 1000 * (1 / 2 ^ 53) * X ≤ 1001 / 1000 * (1 / 2 ^ 53) * (1113 / 10000) :=
      mul_le_mul_of_nonneg_left hX1 (by positivity)
    linarith
  have hta := tan_small a ha
  have htb := tan_small b hb
  have hd := tan_diff_small a b ha hb
  rw [hX] at hta
  refine ⟨hta, ?_, ?_, ?_⟩
  · have := abs_sub_abs_le_abs_sub W (Real.tan a)
    linarith
  · have : 10204 / 10000 * |b| ≤ 10204 / 10000 * (X + (1001 / 1000 * 𝐮 * X + 1 / 2 ^ 59)) :=
      mul_le_mul_of_nonneg_left hb' (by norm_num)
    rw [hu] at this
    have : 10204 / 10000 * (1001 / 1000 * (1 / 2 ^ 53) * X) ≤ 10204 / 10000 * (1001 / 1000 *
        (1 / 2 ^ 53) * (1113 / 10000)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX1 (by positivity)) (by norm_num)
    have : (10204 / 10000 : ℝ) * (1001 / 1000 * (1 / 2 ^ 53) * (1113 / 10000)) +
        10204 / 10000 * (1 / 2 ^ 59) ≤ 1 / 2 ^ 55 := by norm_num
    linarith
  · exact hd.trans (mul_le_mul_of_nonneg_left hab (by norm_num))

/-- The real error from `|a| = 0.05` on. -/
theorem big_close_hi (v W τ a b X : ℝ) (hv : v = 1 ∨ v = -1) (hX : |a| = X)
    (hX0 : 5 / 100 ≤ X) (hX1 : X ≤ 1113 / 10000)
    (hW : |W - Real.tan a| ≤ even_err X)
    (hτ : |τ - Tv v W| ≤ 2 * (24 / 10 * 𝐮 * (X + 900 * η) + 4 * η))
    (hab : |a - b| ≤ 1001 / 1000 * 𝐮 * X + 1 / 2 ^ 59) :
    |τ - Tv v (Real.tan b)| < 95 / 100 * 𝐮 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have hX0' : 0 ≤ X := by linarith
  have hE := even_err_lin X hX0' hX1
  obtain ⟨hta, hWb, htb, hd⟩ := three_small W a b X (even_err X) hX hX1 hW hab
  have hm : 10204 / 10000 * X + even_err X ≤ 1136 / 10000 := by
    rw [hu, hη] at hE
    linarith
  have hm' : 10204 / 10000 * X + 1 / 2 ^ 55 ≤ 1136 / 10000 := by
    have : (10204 / 10000 : ℝ) * (1113 / 10000) + 1 / 2 ^ 55 ≤ 1136 / 10000 := by norm_num
    linarith
  have c1 := Tv_close v W (Real.tan a) (1136 / 10000) hv (by linarith) (by linarith)
    (by norm_num)
  have c2 := Tv_close v (Real.tan a) (Real.tan b) (1136 / 10000) hv (by linarith) (by linarith)
    (by norm_num)
  have t1 := abs_sub_le τ (Tv v W) (Tv v (Real.tan b))
  have t2 := abs_sub_le (Tv v W) (Tv v (Real.tan a)) (Tv v (Real.tan b))
  norm_num at c1 c2
  simp only [hu, hη] at hτ hE hd ⊢
  linarith

/-- The real error below `|a| = 0.05`. -/
theorem big_close_lo (v W τ a b X : ℝ) (hv : v = 1 ∨ v = -1) (hX : |a| = X)
    (hX1 : X ≤ 5 / 100)
    (hW : |W - Real.tan a| ≤ even_err X)
    (hτ : |τ - Tv v W| ≤ 2 * (24 / 10 * 𝐮 * (X + 900 * η) + 4 * η))
    (hab : |a - b| ≤ 1001 / 1000 * 𝐮 * X + 1 / 2 ^ 59) :
    |τ - Tv v (Real.tan b)| ≤ 45 / 100 * 𝐮 ∧ 9 / 10 ≤ |Tv v (Real.tan b)| ∧
      |Tv v (Real.tan b)| ≤ 2 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have hX0' : 0 ≤ X := hX ▸ abs_nonneg _
  have hE := even_err_lin X hX0' (by linarith)
  obtain ⟨hta, hWb, htb, hd⟩ := three_small W a b X (even_err X) hX (by linarith) hW hab
  have hm : 10204 / 10000 * X + even_err X ≤ 511 / 10000 := by
    rw [hu, hη] at hE
    linarith
  have hm' : 10204 / 10000 * X + 1 / 2 ^ 55 ≤ 511 / 10000 := by
    have : (10204 / 10000 : ℝ) * (5 / 100) + 1 / 2 ^ 55 ≤ 511 / 10000 := by norm_num
    linarith
  have c1 := Tv_close v W (Real.tan a) (511 / 10000) hv (by linarith) (by linarith)
    (by norm_num)
  have c2 := Tv_close v (Real.tan a) (Real.tan b) (511 / 10000) hv (by linarith) (by linarith)
    (by norm_num)
  have t1 := abs_sub_le τ (Tv v W) (Tv v (Real.tan b))
  have t2 := abs_sub_le (Tv v W) (Tv v (Real.tan a)) (Tv v (Real.tan b))
  have hB : |Real.tan b| ≤ 511 / 10000 := by linarith
  have hB' := abs_le.mp hB
  refine ⟨?_, ?_⟩
  · norm_num at c1 c2
    simp only [hu, hη] at hτ hE hd ⊢
    linarith
  · rcases hv with rfl | rfl
    · rw [Tv_one _ (ne_of_gt (by linarith)), abs_of_pos (div_pos (by linarith) (by linarith))]
      constructor
      · rw [le_div_iff₀ (by linarith)]; linarith
      · rw [div_le_iff₀ (by linarith)]; linarith
    · rw [Tv_negOne _ (ne_of_lt (by linarith)), abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + Real.tan b),
        abs_of_neg (by linarith : Real.tan b - 1 < 0)]
      constructor
      · rw [le_div_iff₀ (by linarith)]; linarith
      · rw [div_le_iff₀ (by linarith)]; linarith

#print axioms tan_quarter
#print axioms big_close_hi
#print axioms big_close_lo

end Verified.Examples.TanBigClose
