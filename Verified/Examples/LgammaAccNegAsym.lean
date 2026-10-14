import Verified.Examples.LgammaAccNeg

/-!
**Stirling's series at a negative argument** of `Lgamma.accurate`, which evaluates
`log Γ (1 + |x|)` at the double-double `fastTwoSum |x| 1` (`asym_input`).  From 15/4 to 21/2
the triple satisfies `LgammaAccNeg.NegSmall` (`asym_small`), with `log Γ (1 + |x|) ≤ 17`
(`lgamma_le_17`).
-/

namespace Verified.Examples.LgammaAccNegAsym
open CodeLib.IEEE64 LeanExe.ProofKit Tgamma TgammaDD LgammaAccWin LgammaLogAccKern LgammaAccNeg
open Real GammaBasic

set_option exponentiation.threshold 4096

/-- **The input of the series**: `fastTwoSum x 1` is exact, with a small low part. -/
theorem asym_input (x : Float) (hx : Finite x.toBits) (h1 : 15 / 4 ≤ value x.toBits)
    (h2 : value x.toBits ≤ 2 ^ 800) (xh xl : Float) (hT : fastTwoSum x 1.0 = (xh, xl)) :
    Finite xh.toBits ∧ Finite xl.toBits ∧ value xh.toBits + value xl.toBits = value x.toBits + 1 ∧
      15 / 4 ≤ value xh.toBits ∧ value xh.toBits ≤ 2 ^ 801 ∧
      |value xl.toBits| ≤ value xh.toBits / 2 ^ 51 ∧ |value xl.toBits| ≤ 1 ∧
      value xh.toBits ≤ value x.toBits + 2 := by
  obtain ⟨f1, f2, hs, hl1, hl2⟩ := fastTwoSum_spec x 1.0 hx c10.1
    (by rw [c10.2, abs_one, abs_of_pos (by linarith : (0 : ℝ) < value x.toBits)]; linarith)
    (by rw [abs_of_pos (by linarith : (0 : ℝ) < value x.toBits)]
        linarith [(by norm_num : (2 : ℝ) ^ 800 < 2 ^ 900)])
  rw [hT] at f1 f2 hs hl1 hl2
  dsimp only at f1 f2 hs hl1 hl2
  rw [c10.2, abs_one] at hl1
  rw [c10.2] at hs
  have hxl := abs_le.mp hl1
  have hxh : 15 / 4 ≤ value xh.toBits := by linarith
  rw [abs_of_pos (by linarith : (0 : ℝ) < value xh.toBits)] at hl2
  refine ⟨f1, f2, hs, hxh, by linarith [(by norm_num : (2 : ℝ) ^ 800 + 2 ≤ 2 ^ 801)], ?_, hl1,
    by linarith⟩
  have : (1 : ℝ) / 2 ^ 1074 ≤ value xh.toBits / 2 ^ 52 := by
    rw [le_div_iff₀ (by positivity)]
    calc (1 : ℝ) / 2 ^ 1074 * 2 ^ 52 = 1 / 2 ^ 1022 := by norm_num
      _ ≤ value xh.toBits := by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1022 ≤ 15 / 4)]
  have e : value xh.toBits / 2 ^ 51 = value xh.toBits / 2 ^ 52 + value xh.toBits / 2 ^ 52 := by ring
  rw [e]
  linarith

/-- **`log Γ y ≤ 17` from 2 to 23/2**: `Γ (23/2) ≤ 0.8863 · 13427062 < e^17`. -/
theorem lgamma_le_17 (y : ℝ) (h1 : 2 ≤ y) (h2 : y ≤ 23 / 2) : lgamma y ≤ 17 := by
  have hm := Gamma_strictMonoOn_Ici.monotoneOn (show y ∈ Set.Ici 2 by rw [Set.mem_Ici]; exact h1)
    (show (23 / 2 : ℝ) ∈ Set.Ici 2 by rw [Set.mem_Ici]; norm_num) h2
  have hΓ : Gamma (23 / 2) = Gamma (3 / 2) * ∏ j ∈ Finset.range 10, (3 / 2 + (j : ℝ)) := by
    rw [show (23 / 2 : ℝ) = 3 / 2 + ((10 : ℕ) : ℝ) by norm_num]
    exact gamma_add_nat (notPole_of_neg_one_lt (by norm_num) (by norm_num)) 10
  have hP : ∏ j ∈ Finset.range 10, (3 / 2 + (j : ℝ)) ≤ 13427062 := by
    norm_num [Finset.prod_range_succ]
  obtain ⟨-, g2⟩ := LgammaAccLower.gamma_three_halves_bounds
  have hP0 : 0 ≤ ∏ j ∈ Finset.range 10, (3 / 2 + (j : ℝ)) := by
    norm_num [Finset.prod_range_succ]
  have hge : Gamma (23 / 2) ≤ 12000000 := by
    rw [hΓ]
    nlinarith [mul_le_mul g2 hP hP0 (by norm_num)]
  have he : 12000000 ≤ Real.exp 17 := by
    have h1 := Real.exp_one_gt_d9
    have h17 : Real.exp 17 = Real.exp 1 ^ 17 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h17]
    calc (12000000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 17 := by norm_num
      _ ≤ Real.exp 1 ^ 17 := pow_le_pow_left₀ (by norm_num) h1.le 17
  have hpos : 0 < Gamma y := Gamma_pos_of_pos (by linarith)
  unfold lgamma
  rw [Real.log_le_iff_le_exp hpos]
  linarith

/-- `log Γ y ≥ 0` from 2 on. -/
theorem lgamma_nonneg (y : ℝ) (h1 : 2 ≤ y) : 0 ≤ lgamma y := by
  have hm := Gamma_strictMonoOn_Ici.monotoneOn (show (2 : ℝ) ∈ Set.Ici 2 by
    rw [Set.mem_Ici]) (show y ∈ Set.Ici 2 by rw [Set.mem_Ici]; exact h1) h1
  rw [Gamma_two] at hm
  unfold lgamma
  exact Real.log_nonneg hm

set_option maxHeartbeats 4000000 in
/-- **The series from 15/4 to 21/2** gives `NegSmall` for `log Γ (1 + x)`. -/
theorem asym_small (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAF : LgammaApprox.AsymFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 15 / 4 ≤ value x.toBits) (h2 : value x.toBits < 21 / 2) (xh xl : Float)
    (hT : fastTwoSum x 1.0 = (xh, xl)) :
    NegSmall (lgamma (1 + value x.toBits))
      (Lgamma.asLgammaAsymAccurate Tgamma.logdTable H Lgamma.asymTable xh xl) := by
  obtain ⟨fh, fl, hs, hlo, hhi, hlb, hl1, hxh2⟩ := asym_input x hx h1
    (by linarith [(by norm_num : (21 / 2 : ℝ) ≤ 2 ^ 800)]) xh xl hT
  obtain ⟨f1, f2, f3, he, hr0, hb, hc⟩ := LgammaAsymAcc.asym_spec hF hLA hAF xh xl fh fl hlo hhi
    hlb hl1
  rw [hs, show value x.toBits + 1 = 1 + value x.toBits by ring] at he
  have h48 : value xh.toBits < 48 := by linarith
  have h120 : value xh.toBits < 2 ^ 120 := by linarith [(by norm_num : (48 : ℝ) < 2 ^ 120)]
  rw [if_pos h48, if_pos h120] at he
  generalize Lgamma.asLgammaAsymAccurate Tgamma.logdTable H Lgamma.asymTable xh xl = r
    at f1 f2 f3 he hr0 hb hc ⊢
  have hT17 := lgamma_le_17 (1 + value x.toBits) (by linarith) (by linarith)
  have hT0 := lgamma_nonneg (1 + value x.toBits) (by linarith)
  generalize lgamma (1 + value x.toBits) = T at he hT17 hT0 ⊢
  set a := value r.1.toBits with ha
  have hE : 1 / 2 ^ 87 * T + (1 + value x.toBits) * (1 / 2 ^ 88 + 1 / 2 ^ 91) ≤
      9 / 2 ^ 61 + 1 / 2 ^ 69 + 1 / 2 ^ 84 := by
    have k1 : 1 / 2 ^ 87 * T ≤ 1 / 2 ^ 87 * 17 := mul_le_mul_of_nonneg_left hT17 (by positivity)
    have k2 : (1 + value x.toBits) * (1 / 2 ^ 88 + 1 / 2 ^ 91) ≤ 12 * (1 / 2 ^ 88 + 1 / 2 ^ 91) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have k3 : 1 / 2 ^ 87 * 17 + 12 * (1 / 2 ^ 88 + 1 / 2 ^ 91) ≤
        (9 : ℝ) / 2 ^ 61 + 1 / 2 ^ 69 + 1 / 2 ^ 84 := by norm_num
    linarith
  have haT : a ≤ 2 * T + 1 := by
    have k := abs_le.mp he
    have kb := abs_le.mp hb
    have kc := abs_le.mp hc
    linarith
  refine ⟨_, a / 2 ^ 40, a / 2 ^ 80, f1, f2, f3, he, ?_, hb, hc, hE, ?_, ?_⟩
  · rw [abs_of_pos hr0]; linarith
  · have : a / 2 ^ 40 ≤ 35 / 2 ^ 40 := div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith [(by norm_num : (35 : ℝ) / 2 ^ 40 ≤ 1 / 2 ^ 34)]
  · have : a / 2 ^ 80 ≤ 35 / 2 ^ 80 := div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith [(by norm_num : (35 : ℝ) / 2 ^ 80 ≤ 1 / 2 ^ 60)]

end Verified.Examples.LgammaAccNegAsym
