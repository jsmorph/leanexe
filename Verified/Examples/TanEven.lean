import Verified.Examples.TanMath
import Verified.Examples.TanStep
import Verified.Examples.TrigNearest

/-!
The even path of `Tan.kernelTan` below `0x3FE59428`: `x + r` rounded, for `|x| = X ≤ 0.67434`
with tail `|y| ≤ X / 2 ^ 52` and `x + y` within `|r'| / 2 ^ 59` of the reduced argument `r'`,
lies within one step of the reference of `tan r'`.  From `X = 0.4642` on, `tan r'` and the sum
lie in `[1/2, 1)` and less than a spacing apart; below, the sum lies within `0.74 u |tan r'|`.
-/

namespace Verified.Examples.TanEven

open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack PolyBound TrigApprox TanWords TanPoly TanMath
  TanStep

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

set_option exponentiation.threshold 1200

theorem B_1022 : B 1022 = 1 / 2 := by
  unfold B
  rw [div_eq_iff (by positivity), show (1074 : Nat) = (1022 + 51) + 1 by norm_num, pow_succ]
  ring

theorem S_1022 : S 1022 = 1 / 2 ^ 53 := by
  unfold S
  rw [show (1074 : Nat) = 1021 + 53 by norm_num, pow_add]
  field_simp

theorem B_1023 : B 1023 = 1 := by
  unfold B
  norm_num

theorem S_1023 : S 1023 = 1 / 2 ^ 52 := by
  unfold S
  rw [show (1074 : Nat) = 1022 + 52 by norm_num, pow_add]
  field_simp

/-- `|tan s| = tan |s|` below `π/2`. -/
theorem abs_tan (s : ℝ) (h : |s| < Real.pi / 2) : |Real.tan s| = Real.tan |s| := by
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs] at h ⊢
    exact abs_of_nonneg (Real.tan_nonneg_of_nonneg_of_le_pi_div_two hs h.le)
  · rw [abs_of_neg hs] at h ⊢
    rw [Real.tan_neg] at *
    have := Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith : (0 : ℝ) ≤ -s) h.le
    rw [Real.tan_neg] at this
    rw [abs_of_nonpos (by linarith)]

/-- Bounds on `tan` on `[0, 0.6745]`. -/
theorem tan_bounds (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 6745 / 10000) :
    s ≤ Real.tan s ∧ Real.tan s ≤ 8875 / 10000 ∧
      (4642 / 10000 ≤ s → 5001 / 10000 ≤ Real.tan s) := by
  have hpi := Real.pi_gt_three
  have hc := cos_lower s (by rw [abs_of_nonneg h0]; exact h1)
  refine ⟨?_, ?_, ?_⟩
  · rcases h0.lt_or_eq with h | h
    · exact (Real.lt_tan h (by linarith)).le
    · rw [← h, Real.tan_zero]
  · rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (by linarith)]
    have hs : Real.sin s ≤ s := by
      rcases h0.lt_or_eq with h | h
      · exact (Real.sin_lt h).le
      · rw [← h, Real.sin_zero]
    nlinarith
  · intro hs
    have hm : Real.tan (4642 / 10000) ≤ Real.tan s := by
      rcases hs.lt_or_eq with h | h
      · exact (Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) (by linarith) h).le
      · rw [h]
    refine le_trans ?_ hm
    have hsin := Real.sin_gt_sub_cube (x := 4642 / 10000) (by norm_num)
    have hcb := Real.cos_bound (x := 4642 / 10000) (by norm_num)
    have hcu := (abs_le.mp hcb).2
    have hc0 := cos_lower (4642 / 10000) (by norm_num)
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ (by linarith)]
    norm_num at hsin hcu ⊢
    nlinarith


/-- The exact sum `x + r` approaches `tan r'` within the bound `even_err X`. -/
noncomputable def even_err (X : ℝ) : ℝ :=
  1336 / 1000 * 𝐮 * X ^ 3 + 36 / 10 * 𝐮 * X ^ 5 + 13 * 𝐮 * 𝐮 * X ^ 3 + 30 * 𝐮 * 𝐮 * X +
    9 * η + X * ((59 / 64) / 2 ^ 59) + X * (1 + 1 / 2 ^ 50) / 2 ^ 59 / (76 / 100) ^ 2

set_option maxHeartbeats 2000000 in
/-- The correction's rounding and the kernel polynomial's error together. -/
theorem even_sum (x y : UInt64) (r X : ℝ) (hxf : Finite x) (hyf : Finite y)
    (hX : |value x| = X) (hX1 : X ≤ 67434 / 100000) (hy : |value y| ≤ X / 2 ^ 52)
    (har : |value x + value y - r| ≤ |r| / 2 ^ 59) :
    Finite (corrW x y) ∧ |value (corrW x y)| ≤ 1 / 2 ∧
      |value x + value (corrW x y) - Real.tan r| ≤ even_err X ∧
      X * (1 - 1 / 2 ^ 50) ≤ |r| ∧ |r| ≤ X * (1 + 1 / 2 ^ 50) := by
  have h0 : 0 ≤ X := hX ▸ abs_nonneg _
  obtain ⟨⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩, ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩, hX1', hXX⟩ := pow_facts X h0 (by linarith)
  obtain ⟨M, ⟨⟨hcf, hce⟩, hcm⟩, hM⟩ := corr_AB x y X hxf hyf hX (by linarith) hy
  have hcv := F64Approx.Approx.abs_le ⟨hcf, hce⟩ hcm
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  -- `|r|` against `X`.
  have hr1 := abs_sub_abs_le_abs_sub (value x + value y) r
  have hr2 := abs_sub_abs_le_abs_sub r (value x + value y)
  rw [abs_sub_comm] at hr2
  have hxy1 := abs_add_le (value x) (value y)
  have hxy2 := abs_sub_abs_le_abs_sub (value x) (-value y)
  rw [sub_neg_eq_add, abs_neg] at hxy2
  rw [hX] at hxy1 hxy2
  have hrX1 : |r| ≤ X * (1 + 1 / 2 ^ 50) := by
    have : |r| * (1 - 1 / 2 ^ 59) ≤ X * (1 + 1 / 2 ^ 52) := by nlinarith
    nlinarith [abs_nonneg r]
  have hrX0 : X * (1 - 1 / 2 ^ 50) ≤ |r| := by
    have : X * (1 - 1 / 2 ^ 52) ≤ |r| * (1 + 1 / 2 ^ 59) := by nlinarith
    nlinarith [abs_nonneg r]
  refine ⟨hcf, by simp only [unitRoundoff64, multiplicationUnderflowEpsilon] at hcv; linarith,
    ?_, hrX0, hrX1⟩
  -- The kernel's expansion of `tan (x + y)`.
  have hexp := tan_tail_expand (value x) (value y) (by rw [hX]; exact hX1) (by rw [hX]; exact hy)
  rw [hX, ← corrT_eval] at hexp
  have hab : |value x + value y| ≤ 6745 / 10000 := by linarith
  have hr6 : |r| ≤ 6745 / 10000 := by nlinarith
  have htd := tan_diff (value x + value y) r hab hr6
  have htd' : |Real.tan (value x + value y) - Real.tan r| ≤
      X * (1 + 1 / 2 ^ 50) / 2 ^ 59 / (76 / 100) ^ 2 := by
    refine htd.trans (div_le_div_of_nonneg_right (har.trans ?_) (by norm_num))
    exact div_le_div_of_nonneg_right hrX1 (by norm_num)
  have hyy : |value y| * (9 / 10 * X ^ 4 + X ^ 2 / 2 ^ 57) ≤
      X / 2 ^ 52 * (9 / 10 * X ^ 4 + X ^ 2 / 2 ^ 57) :=
    mul_le_mul_of_nonneg_right hy (by positivity)
  have hy2 : value y ^ 2 ≤ X ^ 2 / 2 ^ 104 := by
    rw [← sq_abs]
    have := pow_le_pow_left₀ (abs_nonneg _) hy 2
    rw [div_pow, ← pow_mul] at this
    exact this
  have hce' := abs_le.mp hce
  have hexp' := abs_le.mp hexp
  have htd'' := abs_le.mp htd'
  unfold even_err
  rw [abs_le]
  simp only [hu, hη] at hce' hexp' ⊢
  constructor <;> linarith [hce'.1, hce'.2, hexp'.1, hexp'.2, htd''.1, htd''.2]

#print axioms even_sum

theorem even_err_big (X : ℝ) (h0 : 0 ≤ X) (h1 : X ≤ 67434 / 100000) : even_err X < 1 / 2 ^ 53 := by
  have h3 : X ^ 3 ≤ (67434 / 100000) ^ 3 := pow_le_pow_left₀ h0 h1 3
  have h5 : X ^ 5 ≤ (67434 / 100000) ^ 5 := pow_le_pow_left₀ h0 h1 5
  unfold even_err
  simp only [unitRoundoff64, multiplicationUnderflowEpsilon]
  norm_num at h3 h5 ⊢
  nlinarith

theorem even_err_small (X : ℝ) (h0 : 1 / 2 ^ 70 ≤ X) (h1 : X ≤ 4643 / 10000) :
    even_err X ≤ 74 / 100 * 𝐮 * (X * (1 - 1 / 2 ^ 50)) := by
  have hX0 : 0 ≤ X := le_trans (by positivity) h0
  have h2 : X ^ 2 ≤ (4643 / 10000) ^ 2 := pow_le_pow_left₀ hX0 h1 2
  have h3 : X ^ 3 ≤ (4643 / 10000) ^ 2 * X := by
    rw [show X ^ 3 = X ^ 2 * X by ring]
    exact mul_le_mul_of_nonneg_right h2 hX0
  have h4 : X ^ 4 ≤ ((4643 / 10000) ^ 2) ^ 2 := by
    rw [show X ^ 4 = (X ^ 2) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have h5 : X ^ 5 ≤ ((4643 / 10000) ^ 2) ^ 2 * X := by
    rw [show X ^ 5 = X ^ 4 * X by ring]
    exact mul_le_mul_of_nonneg_right h4 hX0
  unfold even_err
  simp only [unitRoundoff64, multiplicationUnderflowEpsilon]
  norm_num at h0 h3 h5 ⊢
  nlinarith

theorem near_tan (t r : ℝ) (hd : |t - Real.tan r| < 1 / 2 ^ 53) (hr : |r| ≤ 6745 / 10000)
    (hT : 5001 / 10000 ≤ |Real.tan r|) :
    (B 1022 ≤ |Real.tan r| ∧ |Real.tan r| ≤ 2 * B 1022) ∧ (B 1022 ≤ |t| ∧ |t| ≤ 2 * B 1022) ∧
      0 < t * Real.tan r := by
  have hpi := Real.pi_gt_three
  have hTa := abs_tan r (by linarith)
  have hTu := (tan_bounds |r| (abs_nonneg r) hr).2.1
  rw [B_1022]
  have hd' := abs_lt.mp hd
  have ht1 := abs_sub_abs_le_abs_sub t (Real.tan r)
  have ht2 := abs_sub_abs_le_abs_sub (Real.tan r) t
  rw [abs_sub_comm] at ht2
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
  rcases le_or_gt 0 (Real.tan r) with h | h
  · rw [abs_of_nonneg h] at hT
    nlinarith
  · rw [abs_of_neg h] at hT
    nlinarith

set_option maxHeartbeats 1000000 in
/-- The even path below `0x3FE59428`. -/
theorem even_within (x y : UInt64) (r X : ℝ) (hxf : Finite x) (hyf : Finite y)
    (hX : |value x| = X) (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 67434 / 100000)
    (hy : |value y| ≤ X / 2 ^ 52) (har : |value x + value y - r| ≤ |r| / 2 ^ 59) :
    F64SignedRounding.WithinSteps 1 (Real.tan r) (Wasm.IEEE64.add x (corrW x y)) := by
  obtain ⟨hcf, hcb, hd, hr0, hr1⟩ := even_sum x y r X hxf hyf hX hX1 hy har
  have hX0' : 0 ≤ X := le_trans (by positivity) hX0
  have hb : |value x + value (corrW x y)| < 2 ^ 1023 := by
    have := abs_add_le (value x) (value (corrW x y))
    rw [hX] at this
    have h4 : (4 : ℝ) < 2 ^ 1023 := four_lt 1023 (by norm_num)
    linarith
  obtain ⟨hfin, -⟩ := F64AddBounds.add_real_relative x _ hxf hcf hb
  have hnear : ∀ v : UInt64, Finite v → |value (Wasm.IEEE64.add x (corrW x y)) -
      (value x + value (corrW x y))| ≤ |value v - (value x + value (corrW x y))| :=
    fun v _ => TrigNearest.add_nearest x _ hxf hcf hb v
  have hr6 : |r| ≤ 6745 / 10000 := by nlinarith
  have hpi := Real.pi_gt_three
  have hTa := abs_tan r (by linarith)
  obtain ⟨hlo, hhi, hmid⟩ := tan_bounds |r| (abs_nonneg r) hr6
  rcases le_or_gt (4643 / 10000) X with hbig | hsmall
  · have hT : 5001 / 10000 ≤ |Real.tan r| := by
      rw [hTa]
      exact hmid (by nlinarith)
    have hd' : |value x + value (corrW x y) - Real.tan r| < 1 / 2 ^ 53 :=
      lt_of_le_of_lt hd (even_err_big X hX0' hX1)
    obtain ⟨hT', ht', hs⟩ := near_tan _ r hd' hr6 hT
    exact near_bin _ _ (Real.tan r) 1022 (by norm_num) (by norm_num) hfin hnear hT' ht' hs
      (by rw [S_1022]; exact hd')
  · refine near_rel _ _ (Real.tan r) hfin hnear ?_ ?_ ?_
    · rw [hTa]
      have : 1 / 2 ^ 1000 ≤ |r| := le_trans (by
        have : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 70 * (1 - 1 / 2 ^ 50) := by norm_num
        nlinarith) hr0
      linarith
    · rw [hTa]
      have : (8875 / 10000 : ℝ) ≤ 2 ^ 1000 := by norm_num
      linarith
    · refine hd.trans ((even_err_small X hX0 hsmall.le).trans ?_)
      have hu : (0 : ℝ) ≤ 74 / 100 * 𝐮 := by unfold unitRoundoff64; positivity
      rw [hTa]
      exact mul_le_mul_of_nonneg_left (hr0.trans hlo) hu

#print axioms even_within

end Verified.Examples.TanEven
