import Library.Numerics.Float64.Tan.TanOdd

/-!
The error of `Tan.kernelTan` from `0x3FE59428` on, in real numbers: with `x'` the argument,
`r` the computed correction, and `W = x' + r`, the computed `x' - (w ^ 2/(w + v) - r)` lies within
`2.4 u |x'| + 4 η` of `W v/(W + v)`, for `v = ±1` and `|x'| ≤ 1/8`.  The rounding of `w` enters
only through `W ^ 2/(W + v) - w ^ 2/(w + v)`, which carries a factor of the size of `|x'|`.
-/

namespace Library.Numerics.Float64.Tan.TanBigReal

open CodeLib.IEEE64 LeanExe.ProofKit TanOdd

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

set_option exponentiation.threshold 1200

theorem near_one (a v : ℝ) (hv : |v| = 1) : 1 - |a| ≤ |a + v| := by
  have h := abs_sub_abs_le_abs_sub v (-a)
  rw [sub_neg_eq_add, abs_neg, add_comm, hv] at h
  exact h

/-- The rounding of `w` in `w ^ 2/(w + v)`. -/
theorem bigA (W wv v X : ℝ) (hv : |v| = 1) (hX : X ≤ 1 / 8) (hWb : |W| ≤ 101 / 100 * X)
    (hw : |wv - W| ≤ 𝐮 * |W|) :
    |W * W / (W + v) - wv * wv / (wv + v)| ≤ 37 / 100 * 𝐮 * X := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hX0 : 0 ≤ X := by linarith [abs_nonneg W]
  have hwvb : |wv| ≤ 102 / 100 * X := by
    have := abs_sub_abs_le_abs_sub wv W
    rw [hu] at hw
    linarith
  have hWv : 873 / 1000 ≤ |W + v| := by have := near_one W v hv; linarith
  have hwv : 872 / 1000 ≤ |wv + v| := by have := near_one wv v hv; linarith
  have hWv0 : W + v ≠ 0 := fun h => by rw [h, abs_zero] at hWv; norm_num at hWv
  have hwv0 : wv + v ≠ 0 := fun h => by rw [h, abs_zero] at hwv; norm_num at hwv
  have hid : W * W / (W + v) - wv * wv / (wv + v) =
      (W - wv) * (W * wv + v * (W + wv)) / ((W + v) * (wv + v)) := by
    rw [div_sub_div _ _ hWv0 hwv0]
    congr 1
    ring
  have hD : 873 / 1000 * (872 / 1000) ≤ |W + v| * |wv + v| :=
    mul_le_mul hWv hwv (by norm_num) (abs_nonneg _)
  rw [hid, abs_div, abs_mul, abs_mul, div_le_iff₀ (by linarith)]
  have e1 : |W - wv| ≤ 𝐮 * (101 / 100 * X) := by
    rw [abs_sub_comm]
    exact hw.trans (mul_le_mul_of_nonneg_left hWb (by rw [hu]; positivity))
  have e2 : |W * wv + v * (W + wv)| ≤ 216 / 100 * X := by
    have h1 := abs_add_le (W * wv) (v * (W + wv))
    rw [abs_mul, abs_mul, hv, one_mul] at h1
    have h2 := abs_add_le W wv
    have h3 : |W| * |wv| ≤ 101 / 100 * X * (102 / 100 * X) :=
      mul_le_mul hWb hwvb (abs_nonneg _) (by positivity)
    have h4 : X * X ≤ X * (1 / 8) := mul_le_mul_of_nonneg_left hX hX0
    linarith
  have e3 := mul_le_mul e1 e2 (abs_nonneg _) (by rw [hu]; positivity)
  have e4 : 37 / 100 * 𝐮 * X * (873 / 1000 * (872 / 1000)) ≤
      37 / 100 * 𝐮 * X * (|W + v| * |wv + v|) :=
    mul_le_mul_of_nonneg_left hD (by rw [hu]; positivity)
  have h4 : X * X ≤ X * (1 / 8) := mul_le_mul_of_nonneg_left hX hX0
  rw [hu] at e3 e4 ⊢
  linarith

/-- The roundings of `w ^ 2` and `w + v` in `w ^ 2/(w + v)`. -/
theorem bigB (wv ww den v X : ℝ) (hv : |v| = 1) (hX0 : 0 ≤ X) (hX : X ≤ 1 / 8)
    (hwvb : |wv| ≤ 102 / 100 * X) (hww : |ww - wv * wv| ≤ 𝐮 * |wv * wv| + η)
    (hden : |den - (wv + v)| ≤ 𝐮 * |wv + v|) :
    |wv * wv / (wv + v) - ww / den| ≤ 30 / 100 * 𝐮 * X + 2 * η ∧
      |ww / den| ≤ 15 / 100 * X + 2 * η := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have hwv : 872 / 1000 ≤ |wv + v| := by have := near_one wv v hv; linarith
  have hwv0 : wv + v ≠ 0 := fun h => by rw [h, abs_zero] at hwv; norm_num at hwv
  have hwvu : |wv + v| ≤ 2 := by
    have := abs_add_le wv v
    rw [hv] at this
    linarith
  have hdl : 87 / 100 ≤ |den| := by
    have := abs_sub_abs_le_abs_sub (wv + v) den
    rw [abs_sub_comm] at this
    have : 𝐮 * |wv + v| ≤ 𝐮 * 2 := mul_le_mul_of_nonneg_left hwvu (by rw [hu]; positivity)
    rw [hu] at this hden
    linarith
  have hden0 : den ≠ 0 := fun h => by rw [h, abs_zero] at hdl; norm_num at hdl
  have hsq : wv * wv ≤ 1041 / 1000 * X * X := by
    have h1 : |wv| * |wv| ≤ 102 / 100 * X * (102 / 100 * X) :=
      mul_le_mul hwvb hwvb (abs_nonneg _) (by positivity)
    rw [← abs_mul, abs_mul_self] at h1
    have := mul_self_nonneg X
    linarith
  have hsq0 : 0 ≤ wv * wv := mul_self_nonneg wv
  have h4 : X * X ≤ X * (1 / 8) := mul_le_mul_of_nonneg_left hX hX0
  rw [abs_mul_self] at hww
  -- `ρ`, the relative error of `den`.
  have hρ : |(den - (wv + v)) / (wv + v)| ≤ 𝐮 := by
    rw [abs_div, div_le_iff₀ (by linarith)]
    exact hden
  have hid : wv * wv / (wv + v) - ww / den =
      (wv * wv * ((den - (wv + v)) / (wv + v)) - (ww - wv * wv)) / den := by
    field_simp <;> ring
  have hn : |wv * wv * ((den - (wv + v)) / (wv + v)) - (ww - wv * wv)| ≤
      wv * wv * 𝐮 + (𝐮 * (wv * wv) + η) := by
    have h1 := sub_abs (wv * wv * ((den - (wv + v)) / (wv + v))) (ww - wv * wv)
    rw [abs_mul, abs_mul_self] at h1
    have h2 := mul_le_mul_of_nonneg_left hρ hsq0
    linarith
  have hw2 : |ww| ≤ wv * wv * (1 + 𝐮) + η := by
    have := abs_sub_abs_le_abs_sub ww (wv * wv)
    rw [abs_mul_self] at this
    linarith
  rw [hu, hη] at hn hw2
  refine ⟨?_, ?_⟩
  · rw [hid, abs_div, div_le_iff₀ (by linarith)]
    have : (30 / 100 * (1 / 2 ^ 53) * X + 2 * (1 / 2 ^ 1075)) * (87 / 100) ≤
        (30 / 100 * (1 / 2 ^ 53) * X + 2 * (1 / 2 ^ 1075)) * |den| :=
      mul_le_mul_of_nonneg_left hdl (by positivity)
    rw [hu, hη]
    linarith
  · rw [abs_div, div_le_iff₀ (by linarith)]
    have : (15 / 100 * X + 2 * (1 / 2 ^ 1075)) * (87 / 100) ≤
        (15 / 100 * X + 2 * (1 / 2 ^ 1075)) * |den| :=
      mul_le_mul_of_nonneg_left hdl (by positivity)
    rw [hη]
    linarith

/-- The computed `x' - (w ^ 2/(w + v) - r)` against `W v/(W + v)`. -/
theorem big_real (v x' r wv ww den q e1 f X : ℝ) (hv : |v| = 1) (hX : |x'| ≤ X)
    (hX1 : X ≤ 1 / 8) (hr : |r| ≤ X / 100)
    (hw : |wv - (x' + r)| ≤ 𝐮 * |x' + r|) (hww : |ww - wv * wv| ≤ 𝐮 * |wv * wv| + η)
    (hden : |den - (wv + v)| ≤ 𝐮 * |wv + v|) (hq : |q - ww / den| ≤ 𝐮 * |ww / den| + η)
    (he1 : |e1 - (q - r)| ≤ 𝐮 * |q - r|) (hf : |f - (x' - e1)| ≤ 𝐮 * |x' - e1|) :
    |f - (x' + r) * v / (x' + r + v)| ≤ 24 / 10 * 𝐮 * X + 4 * η := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  have hX0 : 0 ≤ X := le_trans (abs_nonneg _) hX
  have hWb : |x' + r| ≤ 101 / 100 * X := by
    have := abs_add_le x' r
    linarith
  have hwvb : |wv| ≤ 102 / 100 * X := by
    have := abs_sub_abs_le_abs_sub wv (x' + r)
    rw [hu] at hw
    linarith
  have hA := bigA (x' + r) wv v X hv hX1 hWb hw
  obtain ⟨hB, hqb⟩ := bigB wv ww den v X hv hX0 hX1 hwvb hww hden
  have hWv0 : x' + r + v ≠ 0 := by
    have := near_one (x' + r) v hv
    intro h
    rw [h, abs_zero] at this
    linarith
  have hid : f - (x' + r) * v / (x' + r + v) = (f - (x' - e1)) + (q - r - e1) +
      ((x' + r) * (x' + r) / (x' + r + v) - wv * wv / (wv + v)) +
      (wv * wv / (wv + v) - ww / den) + (ww / den - q) := by
    have h : (x' + r) * v / (x' + r + v) = x' + r - (x' + r) * (x' + r) / (x' + r + v) := by
      rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hWv0]
      ring
    rw [h]
    ring
  rw [hid]
  have t1 := abs_add_le ((f - (x' - e1)) + (q - r - e1) +
      ((x' + r) * (x' + r) / (x' + r + v) - wv * wv / (wv + v)) +
      (wv * wv / (wv + v) - ww / den)) (ww / den - q)
  have t2 := abs_add_le ((f - (x' - e1)) + (q - r - e1) +
      ((x' + r) * (x' + r) / (x' + r + v) - wv * wv / (wv + v))) (wv * wv / (wv + v) - ww / den)
  have t3 := abs_add_le ((f - (x' - e1)) + (q - r - e1))
      ((x' + r) * (x' + r) / (x' + r + v) - wv * wv / (wv + v))
  have t4 := abs_add_le (f - (x' - e1)) (q - r - e1)
  have t5 : |q - r - e1| = |e1 - (q - r)| := abs_sub_comm _ _
  have t6 : |ww / den - q| = |q - ww / den| := abs_sub_comm _ _
  have b1 := sub_abs x' e1
  have b2 := abs_sub_abs_le_abs_sub e1 (q - r)
  have b3 := sub_abs q r
  have b4 := abs_sub_abs_le_abs_sub q (ww / den)
  simp only [hu, hη] at hf he1 hq hA hB hqb ⊢
  linarith

#print axioms big_real

end Library.Numerics.Float64.Tan.TanBigReal
