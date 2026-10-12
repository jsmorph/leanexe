import Verified.Examples.SinhSmall
import Verified.Examples.Expm1FormsOne

/-!
The bounds `E` of `SinhSmall.small_steps` on the ten intervals of `abs(x)` below 1: `2 u τ` on
the path of `expm1` without reduction, and on the path `k = 1` the bound of
`SinhExpm1.near_one_pos` plus the half spacing of `t`, with `SinhCore.check_small` on nine
intervals of `τ = exp abs(x) - 1` between `0.4142` and `1.7183`.
-/

namespace Verified.Examples.SinhSmallCases
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative SinhWords SinhCore SinhSmall

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem exp_443_upper : Real.exp (4430 / 10000) ≤ 1558 / 1000 := by
  obtain ⟨hl, -⟩ := ExpTight.log_two_bounds
  have h1 : Real.exp (4430 / 10000) = Real.exp (Real.log 2) * Real.exp (4430 / 10000 - Real.log 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, Real.exp_log two_pos]
  have h2 : Real.exp (4430 / 10000 - Real.log 2) ≤ Real.exp (-(2499 / 10000)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 := Expm1FormsOne.exp_quarter_upper
  linarith

theorem exp_443_lower : 15572 / 10000 ≤ Real.exp (4430 / 10000) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 4430 / 10000 by norm_num) 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h ⊢
  linarith

/-- The path without reduction, `abs(x) < θ1`. -/
theorem middle_num (τ T : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 4144 / 10000)
    (hT : |T - τ| ≤ 2 * u * τ) :
    2 * u * τ * (1 + 1 / ((1 + T) * (1 + τ))) + 31 / 10 * u * (T * T / (1 + T)) ≤
      2.9375 * u * (τ + τ / (1 + τ)) := by
  have hu : u = 1 / 2 ^ 53 := rfl
  obtain ⟨hT1, hT2⟩ := abs_le.mp hT
  rw [hu] at hT1 hT2 ⊢
  have hT0 : 0 ≤ T := by linarith
  have hTh : T ≤ 4145 / 10000 := by linarith
  set B := 1 / ((1 + T) * (1 + τ)) with hBdef
  set C := τ / (1 + τ) with hCdef
  have h1 : τ * B ≤ C := by
    rw [hBdef, hCdef, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hτ0.le hT0]
  have h2 : T * T / (1 + T) ≤ 4146 / 10000 * τ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hTh hT0, mul_nonneg hτ0.le hT0]
  have h3 : 7 / 10 * τ ≤ C := by
    rw [hCdef, le_div_iff₀ (by linarith)]; nlinarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  nlinarith

/-- `sinh` below 1 for positive results. -/
theorem sinh_small_pos (x : Float) (hxf : Finite x.toBits) (hlo : 1 / 2 ^ 28 ≤ |value x.toBits|)
    (hhi : |value x.toBits| < 1) :
    F64SignedRounding.WithinSteps 3 (Real.sinh |value x.toBits|)
      (0.5 * (2.0 * Tanh.expm1 x.abs - Tanh.expm1 x.abs * Tanh.expm1 x.abs /
        (Tanh.expm1 x.abs + 1.0))).toBits := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  obtain ⟨haf, hav⟩ := abs_float x hxf
  obtain ⟨hθ1, hθ1', hθ2, -, -⟩ := Expm1Near.threshold_bounds
  set θ1 := value (UInt64.ofNat (1071001155 * 2 ^ 32))
  set θ2 := value (UInt64.ofNat (1072734898 * 2 ^ 32))
  set A := |value x.toBits| with hAdef
  set τ := Real.exp A - 1 with hτdef
  have hτA : A ≤ τ := by rw [hτdef]; linarith [Real.add_one_le_exp A]
  have hτ0 : 0 < τ := lt_of_lt_of_le (lt_of_lt_of_le (by positivity) hlo) hτA
  have hτ1 : τ ≤ 17183 / 10000 := by
    have h1 : Real.exp A ≤ Real.exp 1 := Real.exp_le_exp.mpr hhi.le
    have h2 := Real.exp_one_lt_d9
    rw [hτdef]; norm_num at h2; linarith
  by_cases hm : A < θ1
  · obtain ⟨htf, hT⟩ := CoshSmall.expm1_small x.abs haf (by rw [hav]; exact abs_nonneg _)
      (by rw [hav]; exact hm)
    rw [hav] at hT
    have hτm : τ ≤ 4144 / 10000 := by
      have := CoshSmall.exp_upper_small A (by linarith)
      rw [hτdef]; linarith
    refine small_steps x hlo hhi (2 * u * τ) htf hT (by rw [hu]; nlinarith) ?_
    exact middle_num τ _ hτ0 hτm hT
  push Not at hm
  obtain ⟨S, hn, hB2, hB1, hB0⟩ := SinhExpm1.near_one_pos x.abs haf (by rw [hav]; exact hm)
    (by rw [hav]; show A < θ2; linarith)
  rw [hav] at hB2 hB1 hB0
  have htf := (nearest_finite S _ hn).1
  set T := value (Tanh.expm1 x.abs).toBits with hTdef
  have hτlo : 4142 / 10000 ≤ τ := by
    have := exp_lower A (by linarith)
    rw [hτdef]; linarith
  -- The half spacing of `t` below `1/2`, `1`, and `2`.
  have hS0 : 0 ≤ S := by
    have := abs_le.mp hB2
    have : 4802 / 10000 * u + 3 * η + 2 * (1 / 2 ^ 55) ≤ 1 / 10 ^ 10 := by
      rw [hu, hη]; norm_num
    linarith
  have hhalf : ∀ g : Nat, g ≤ 2043 → S < 2 ^ (53 + g) / 2 ^ 1074 →
      |T - S| ≤ 2 ^ g / 2 / 2 ^ 1074 :=
    fun g hg hs => F64NearestHalf.nearest_half S _ hn hS0 g hg hs
  have hsmall : ∀ E : ℝ, |T - τ| ≤ E → E ≤ 2 * u →
      E * (1 + 1 / ((1 + T) * (1 + τ))) + 31 / 10 * u * (T * T / (1 + T)) ≤
        2.9375 * u * (τ + τ / (1 + τ)) →
      F64SignedRounding.WithinSteps 3 (Real.sinh A)
        (0.5 * (2.0 * Tanh.expm1 x.abs - Tanh.expm1 x.abs * Tanh.expm1 x.abs /
          (Tanh.expm1 x.abs + 1.0))).toBits := by
    intro E hT hE hnum
    refine small_steps x hlo hhi E htf hT ?_ hnum
    rw [hu] at hE
    have : 2 * (1 / 2 ^ 53 : ℝ) ≤ 4142 / 10000 / 2 ^ 40 := by norm_num
    linarith
  have hcomb : ∀ s0 r0 : ℝ, |S - τ| ≤ s0 → |T - S| ≤ r0 → |T - τ| ≤ s0 + r0 := by
    intro s0 r0 h1 h2
    calc |T - τ| ≤ |T - S| + |S - τ| := abs_sub_le _ _ _
      _ ≤ s0 + r0 := by linarith
  by_cases h443 : A < 4430 / 10000
  · have hS := hB0 h443
    have hτhi : τ ≤ 558 / 1000 := by
      have := Real.exp_le_exp.mpr h443.le
      have := exp_443_upper
      rw [hτdef]; linarith
    by_cases hτ5 : τ < 4999 / 10000
    · have hr := hhalf 1020 (by norm_num) (by
        have h := (abs_le.mp hS).2
        rw [hu] at h
        rw [show (2 : ℝ) ^ (53 + 1020) / 2 ^ 1074 = 1 / 2 by norm_num]
        linarith)
      rw [show (2 : ℝ) ^ 1020 / 2 / 2 ^ 1074 = 1 / 2 ^ 55 by norm_num] at hr
      have hT := hcomb _ _ hS hr
      have hE : 4802 / 10000 * u + 1 / 2 ^ 55 ≤ 7303 / 10000 * u := by rw [hu]; norm_num
      refine hsmall (7303 / 10000 * u) (hT.trans hE) (by rw [hu]; norm_num) ?_
      exact check_small τ T _ (4142 / 10000) (4999 / 10000) _ (2501 / 5000) (417 / 2500)
        (7069 / 10000) (by norm_num) hτlo hτ5.le le_rfl (hT.trans hE) (by rw [hu]; norm_num)
        (by rw [hu]; norm_num) (by rw [hu]; norm_num) (by norm_num) (by rw [hu]; norm_num)
    · push Not at hτ5
      have hr := hhalf 1021 (by norm_num) (by
        have h := (abs_le.mp hS).2
        rw [hu] at h
        rw [show (2 : ℝ) ^ (53 + 1021) / 2 ^ 1074 = 1 by norm_num]
        linarith)
      rw [show (2 : ℝ) ^ 1021 / 2 / 2 ^ 1074 = 1 / 2 ^ 54 by norm_num] at hr
      have hT := hcomb _ _ hS hr
      have hE : 4802 / 10000 * u + 1 / 2 ^ 54 ≤ 9803 / 10000 * u := by rw [hu]; norm_num
      refine hsmall (9803 / 10000 * u) (hT.trans hE) (by rw [hu]; norm_num) ?_
      exact check_small τ T _ (4999 / 10000) (558 / 1000) _ (4447 / 10000) (1 / 5)
        (833 / 1000) (by norm_num) hτ5 hτhi le_rfl (hT.trans hE) (by rw [hu]; norm_num)
        (by rw [hu]; norm_num) (by rw [hu]; norm_num) (by norm_num) (by rw [hu]; norm_num)
  push Not at h443
  have hτ557 : 5572 / 10000 ≤ τ := by
    have := Real.exp_le_exp.mpr h443
    have := exp_443_lower
    rw [hτdef]; linarith
  by_cases h149 : τ ≤ 149 / 100
  · have hS := hB1 h149
    have hS' : |S - τ| ≤ 7303 / 10000 * u := by
      have : 4802 / 10000 * u + 3 * η + 2 * (1 / 2 ^ 56) ≤ 7303 / 10000 * u := by
        rw [hu, hη]; norm_num
      linarith
    by_cases h1 : τ < 9999 / 10000
    · have hr := hhalf 1021 (by norm_num) (by
        have h := (abs_le.mp hS').2
        rw [hu] at h
        rw [show (2 : ℝ) ^ (53 + 1021) / 2 ^ 1074 = 1 by norm_num]
        linarith)
      rw [show (2 : ℝ) ^ 1021 / 2 / 2 ^ 1074 = 1 / 2 ^ 54 by norm_num] at hr
      have hT := hcomb _ _ hS' hr
      have hE : 7303 / 10000 * u + 1 / 2 ^ 54 ≤ 12303 / 10000 * u := by rw [hu]; norm_num
      have hTE := hT.trans hE
      refine hsmall (12303 / 10000 * u) hTE (by rw [hu]; norm_num) ?_
      by_cases h62 : τ ≤ 62 / 100
      · exact check_small τ T _ (5572 / 10000) (62 / 100) _ (33 / 80) (1187 / 5000)
          (9149 / 10000) (by norm_num) hτ557 h62 le_rfl hTE (by rw [hu]; norm_num)
          (by rw [hu]; norm_num) (by rw [hu]; norm_num) (by norm_num) (by rw [hu]; norm_num)
      push Not at h62
      by_cases h7 : τ ≤ 7 / 10
      · exact check_small τ T _ (62 / 100) (7 / 10) _ (953 / 2500) (721 / 2500)
          (5013 / 5000) (by norm_num) h62.le h7 le_rfl hTE (by rw [hu]; norm_num)
          (by rw [hu]; norm_num) (by rw [hu]; norm_num) (by norm_num) (by rw [hu]; norm_num)
      push Not at h7
      by_cases h85 : τ ≤ 85 / 100
      · exact check_small τ T _ (7 / 10) (85 / 100) _ (1731 / 5000) (3907 / 10000)
          (2779 / 2500) (by norm_num) h7.le h85 le_rfl hTE (by rw [hu]; norm_num)
          (by rw [hu]; norm_num) (by rw [hu]; norm_num) (by norm_num) (by rw [hu]; norm_num)
      push Not at h85
      exact check_small τ T _ (85 / 100) (9999 / 10000) _ (2923 / 10000) (5001 / 10000)
        (13093 / 10000) (by norm_num) h85.le h1.le le_rfl hTE (by rw [hu]; norm_num)
        (by rw [hu]; norm_num) (by rw [hu]; norm_num) (by norm_num) (by rw [hu]; norm_num)
    · push Not at h1
      have hr := hhalf 1022 (by norm_num) (by
        have h := (abs_le.mp hS').2
        rw [hu] at h
        rw [show (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 by norm_num]
        linarith)
      rw [show (2 : ℝ) ^ 1022 / 2 / 2 ^ 1074 = 1 / 2 ^ 53 by norm_num] at hr
      have hT := hcomb _ _ hS' hr
      have hE : 7303 / 10000 * u + 1 / 2 ^ 53 ≤ 17303 / 10000 * u := by rw [hu]; norm_num
      have hTE := hT.trans hE
      refine hsmall (17303 / 10000 * u) hTE (by rw [hu]; norm_num) ?_
      by_cases h12 : τ ≤ 12 / 10
      · exact check_small τ T _ (9999 / 10000) (12 / 10) _ (1251 / 5000) (6547 / 10000)
          (14997 / 10000) (by norm_num) h1 h12 le_rfl hTE (by rw [hu]; norm_num)
          (by rw [hu]; norm_num) (by rw [hu]; norm_num) (by norm_num) (by rw [hu]; norm_num)
      push Not at h12
      exact check_small τ T _ (12 / 10) (149 / 100) _ (517 / 2500) (4459 / 5000)
        (17453 / 10000) (by norm_num) h12.le h149 le_rfl hTE (by rw [hu]; norm_num)
        (by rw [hu]; norm_num) (by rw [hu]; norm_num) (by norm_num) (by rw [hu]; norm_num)
  push Not at h149
  have hS' : |S - τ| ≤ 9803 / 10000 * u := by
    have : 4802 / 10000 * u + 3 * η + 2 * (1 / 2 ^ 55) ≤ 9803 / 10000 * u := by
      rw [hu, hη]; norm_num
    linarith
  have hr := hhalf 1022 (by norm_num) (by
    have h := (abs_le.mp hS').2
    rw [hu] at h
    rw [show (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 by norm_num]
    linarith)
  rw [show (2 : ℝ) ^ 1022 / 2 / 2 ^ 1074 = 1 / 2 ^ 53 by norm_num] at hr
  have hT := hcomb _ _ hS' hr
  have hE : 9803 / 10000 * u + 1 / 2 ^ 53 ≤ 19803 / 10000 * u := by rw [hu]; norm_num
  have hTE := hT.trans hE
  refine hsmall (19803 / 10000 * u) hTE (by rw [hu]; norm_num) ?_
  exact check_small τ T _ (149 / 100) (17183 / 10000) _ (807 / 5000) (10863 / 10000)
    (10441 / 5000) (by norm_num) h149.le hτ1 le_rfl hTE (by rw [hu]; norm_num)
    (by rw [hu]; norm_num) (by rw [hu]; norm_num) (by norm_num) (by rw [hu]; norm_num)

#print axioms middle_num
#print axioms sinh_small_pos

end Verified.Examples.SinhSmallCases
