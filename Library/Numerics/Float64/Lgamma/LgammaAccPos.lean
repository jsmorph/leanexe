import Library.Numerics.Float64.Lgamma.LgammaAccPair
import Library.Numerics.Float64.Lgamma.LgammaAccWinSmall
import Library.Numerics.Float64.Lgamma.LgammaAccGrowth
import Library.Numerics.Float64.Lgamma.LgammaAsymAcc

/-!
**The triple of `Lgamma.accurate` at a positive argument**, before the renormalization.
`PosSpec L r` states a triple within `E` of `L` with parts bounded by `A`, `B`, and `C`, whose
error after the renormalization, `E + (B + C)/2^52 + (A + B + C)/2^99 + 2^-1070`, is at most
`|L|/(2^53 + 1)`; `pos_pair` then gives `LgammaAccTail.AccPair`.  `win_pos` derives `PosSpec` from a
window with an absolute error where `|L| ≥ 1/20`, `rel_pos` from a window with a relative error,
and `asym_pos` from Stirling's series from 15/4 to `2^801`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccPos
open CodeLib.IEEE64 LeanExe.ProofKit Tgamma LgammaAccTail LgammaAccWin LgammaAccWinSmall

set_option exponentiation.threshold 4096

/-- The triple at a positive argument. -/
def PosSpec (L : ℝ) (r : Float × Float × Float) : Prop :=
  ∃ A E B C : ℝ, Finite r.1.toBits ∧ Finite r.2.1.toBits ∧ Finite r.2.2.toBits ∧
    |value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits - L| ≤ E ∧
    |value r.1.toBits| ≤ A ∧ |value r.2.1.toBits| ≤ B ∧ |value r.2.2.toBits| ≤ C ∧
    A ≤ 2 ^ 850 ∧ B ≤ 2 ^ 840 ∧ C ≤ 2 ^ 800 ∧ B + C ≤ (|value r.1.toBits| + 1) / 2 ^ 19 ∧
    E + (B + C) / 2 ^ 52 + (A + B + C) / 2 ^ 99 + 1 / 2 ^ 1070 ≤ |L| / (2 ^ 53 + 1)

/-- **The renormalized pair** at a positive argument. -/
theorem pos_pair (L : ℝ) (sx a b c : Float) (hP : PosSpec L (a, b, c))
    (h1 l1 : Float) (e1 : fastTwoSum a b = (h1, l1))
    (l2 ll2 : Float) (e2 : fastTwoSum l1 c = (l2, ll2))
    (h3 l3 : Float) (e3 : fastTwoSum h1 l2 = (h3, l3))
    (l4 ll4 : Float) (e4 : fastTwoSum l3 ll2 = (l4, ll4)) (cond : Bool) :
    AccPair L sx (if cond = true then
        (h3, l4 * (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) l4 *
          Lgamma.copySign (Float.ofBits 0x3E50000000000000) ll4))
      else (h3, l4)) := by
  obtain ⟨A, E, B, C, fa, fb, fc, hE, hA', hB', hC', hA, hB, hC, hBC, hbud⟩ := hP
  have hL : |L| / (2 ^ 53 + 1) ≤ 1 / 2 ^ 50 + |L| / 2 ^ 50 := by
    have : |L| / (2 ^ 53 + 1) ≤ |L| / 2 ^ 50 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num)
    linarith [(by positivity : (0 : ℝ) ≤ 1 / 2 ^ 50)]
  exact LgammaAccPair.norm_pair L sx a b c fa fb fc A E B C hE hA' hB' hC' hA hB hC hBC
    (hbud.trans hL) (fun _ _ _ _ _ => hbud) h1 l1 e1 l2 ll2 e2 h3 l3 e3 l4 ll4 e4 cond

/-- **A window with an absolute error** where `|L| ≥ 1/20`. -/
theorem win_pos (L E B C : ℝ) (r : Float × Float × Float) (hw : WinSpec L E B C r)
    (hL : 1 / 20 ≤ |L|) (hE : E ≤ 9 / 2 ^ 61 + 1 / 2 ^ 69 + 1 / 2 ^ 84) (hB : B ≤ 1 / 2 ^ 39)
    (hC : C ≤ 1 / 2 ^ 83) : PosSpec L r := by
  obtain ⟨f1, f2, f3, he, h4, hb, hc⟩ := hw
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hb
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) hc
  have hL' : (1 / 20) / (2 ^ 53 + 1) ≤ |L| / (2 ^ 53 + 1) :=
    div_le_div_of_nonneg_right hL (by positivity)
  refine ⟨4, E, B, C, f1, f2, f3, he, h4, hb, hc, by norm_num, by linarith, by linarith, ?_, ?_⟩
  · have : (0 : ℝ) ≤ |value r.1.toBits| / 2 ^ 19 := by positivity
    have e : (|value r.1.toBits| + 1) / 2 ^ 19 = |value r.1.toBits| / 2 ^ 19 + 1 / 2 ^ 19 := by ring
    rw [e]
    linarith
  · have k1 : (B + C) / 2 ^ 52 ≤ (1 / 2 ^ 39 + 1 / 2 ^ 83) / 2 ^ 52 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have k2 : (4 + B + C) / 2 ^ 99 ≤ (4 + 1 / 2 ^ 39 + 1 / 2 ^ 83) / 2 ^ 99 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have k3 : 9 / 2 ^ 61 + 1 / 2 ^ 69 + 1 / 2 ^ 84 + (1 / 2 ^ 39 + 1 / 2 ^ 83) / 2 ^ 52 +
        (4 + 1 / 2 ^ 39 + 1 / 2 ^ 83) / 2 ^ 99 + 1 / 2 ^ 1070 ≤ (1 / 20) / (2 ^ 53 + 1) := by
      norm_num
    linarith

/-- **A window with a relative error** `ρ ≤ 2^-64`. -/
theorem rel_pos (L ρ : ℝ) (r : Float × Float × Float) (hr : RelSpec L ρ r) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 1 / 2 ^ 64) (hL : 1 / 2 ^ 1000 ≤ |L|) : PosSpec L r := by
  obtain ⟨f1, f2, f3, he, h4, hb, hc⟩ := hr
  set a := |value r.1.toBits| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  have haL : a ≤ 2 * |L| := by
    have k := abs_sub_abs_le_abs_sub (value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits) L
    have k1 := abs_add_le (value r.1.toBits + value r.2.1.toBits) (value r.2.2.toBits)
    have k2 := abs_add_le (value r.1.toBits) (value r.2.1.toBits)
    have k3 : a ≤ |value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits| +
        |value r.2.1.toBits| + |value r.2.2.toBits| := by
      have := abs_add_le (value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits)
        (-(value r.2.1.toBits + value r.2.2.toBits))
      rw [abs_neg, show value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits +
        -(value r.2.1.toBits + value r.2.2.toBits) = value r.1.toBits by ring] at this
      have := abs_add_le (value r.2.1.toBits) (value r.2.2.toBits)
      linarith
    have hρL : ρ * |L| ≤ |L| / 2 ^ 64 := by
      rw [div_eq_mul_one_div, mul_comm (|L|)]
      exact mul_le_mul_of_nonneg_right hρ (abs_nonneg _)
    nlinarith [abs_nonneg L]
  refine ⟨a, ρ * |L|, a / 2 ^ 20, a / 2 ^ 60, f1, f2, f3, he, le_rfl, hb, hc,
    by linarith, by linarith, by linarith, ?_, ?_⟩
  · have e : (a + 1) / 2 ^ 19 = a / 2 ^ 19 + 1 / 2 ^ 19 := by ring
    rw [e]
    linarith
  · have hρL : ρ * |L| ≤ |L| / 2 ^ 64 := by
      rw [div_eq_mul_one_div, mul_comm (|L|)]
      exact mul_le_mul_of_nonneg_right hρ (abs_nonneg _)
    have k : 1 / 2 ^ 1070 ≤ |L| / 2 ^ 70 := by
      rw [le_div_iff₀ (by positivity)]
      calc 1 / 2 ^ 1070 * 2 ^ 70 = 1 / 2 ^ 1000 := by norm_num
        _ ≤ |L| := hL
    have k2 : |L| / 2 ^ 64 + (a / 2 ^ 20 + a / 2 ^ 60) / 2 ^ 52 + (a + a / 2 ^ 20 + a / 2 ^ 60) / 2 ^ 99 +
        |L| / 2 ^ 70 ≤ |L| / (2 ^ 53 + 1) := by
      have : |L| / (2 ^ 53 + 1) = |L| * (1 / (2 ^ 53 + 1)) := by ring
      rw [this]
      have h1 : (a / 2 ^ 20 + a / 2 ^ 60) / 2 ^ 52 ≤ 2 * |L| * (1 / 2 ^ 72 + 1 / 2 ^ 112) := by
        have : (a / 2 ^ 20 + a / 2 ^ 60) / 2 ^ 52 = a * (1 / 2 ^ 72 + 1 / 2 ^ 112) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right haL (by positivity)
      have h2 : (a + a / 2 ^ 20 + a / 2 ^ 60) / 2 ^ 99 ≤ 2 * |L| * (1 / 2 ^ 99 + 1 / 2 ^ 119 + 1 / 2 ^ 159) := by
        have : (a + a / 2 ^ 20 + a / 2 ^ 60) / 2 ^ 99 = a * (1 / 2 ^ 99 + 1 / 2 ^ 119 + 1 / 2 ^ 159) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right haL (by positivity)
      have h3 : 1 / 2 ^ 64 + 2 * (1 / 2 ^ 72 + 1 / 2 ^ 112) + 2 * (1 / 2 ^ 99 + 1 / 2 ^ 119 + 1 / 2 ^ 159) +
          1 / 2 ^ 70 ≤ 1 / (2 ^ 53 + 1 : ℝ) := by norm_num
      have := mul_le_mul_of_nonneg_left h3 (abs_nonneg L)
      linarith
    linarith

set_option maxHeartbeats 4000000 in
/-- **Stirling's series** at a positive argument from 15/4 to `2^801`. -/
theorem asym_pos (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAF : LgammaApprox.AsymFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 15 / 4 ≤ value x.toBits) (h2 : value x.toBits ≤ 2 ^ 801) :
    PosSpec (GammaBasic.lgamma (value x.toBits))
      (Lgamma.asLgammaAsymAccurate Tgamma.logdTable LgammaLogAccKern.H Lgamma.asymTable x 0.0) := by
  obtain ⟨f1, f2, f3, he, hr0, hb, hc⟩ := LgammaAsymAcc.asym_spec hF hLA hAF x 0.0 hx
    LgammaAccAdd.zero_finite h1 h2
    (by rw [LgammaAccAdd.zero_value, abs_zero]; positivity)
    (by rw [LgammaAccAdd.zero_value, abs_zero]; norm_num)
  rw [LgammaAccAdd.zero_value, add_zero] at he
  generalize Lgamma.asLgammaAsymAccurate Tgamma.logdTable LgammaLogAccKern.H Lgamma.asymTable x
    0.0 = r at f1 f2 f3 he hr0 hb hc ⊢
  generalize hT : GammaBasic.lgamma (value x.toBits) = T at he ⊢
  have hTx : value x.toBits / 8 ≤ T := by rw [← hT]; exact LgammaAccGrowth.growth_small _ h1
  have hTu : T ≤ 2 ^ 812 := by
    rw [← hT]; exact LgammaAccGrowth.lgamma_upper _ (by linarith) (le_trans h2 (by norm_num))
  have hT0 : 15 / 32 ≤ T := by linarith
  set y := value x.toBits with hy
  set a := value r.1.toBits with ha
  -- the error, both cases of the code
  have hE : |a + value r.2.1.toBits + value r.2.2.toBits - T| ≤ T / 2 ^ 63 + y / 2 ^ 86 := by
    refine he.trans ?_
    have k1 : (if y < 48 then (1 : ℝ) / 2 ^ 87 else 1 / 2 ^ 63) ≤ 1 / 2 ^ 63 := by
      split_ifs <;> norm_num
    have k2 : (if y < 2 ^ 120 then (1 : ℝ) / 2 ^ 88 + 1 / 2 ^ 91 else 1 / 2 ^ 86) ≤ 1 / 2 ^ 86 := by
      split_ifs <;> norm_num
    have := mul_le_mul_of_nonneg_right k1 (by linarith : (0 : ℝ) ≤ T)
    have := mul_le_mul_of_nonneg_left k2 (by linarith : (0 : ℝ) ≤ y)
    linarith
  -- the high part against `T`
  have haT : a ≤ 2 * T := by
    have k := abs_le.mp hE
    have kb := abs_le.mp hb
    have kc := abs_le.mp hc
    nlinarith
  have habs : |a| = a := abs_of_pos hr0
  refine ⟨a, T / 2 ^ 63 + y / 2 ^ 86, a / 2 ^ 40, a / 2 ^ 80, f1, f2, f3, hE, habs.le, hb, hc,
    by linarith, by linarith, by linarith, ?_, ?_⟩
  · rw [habs]
    have e : (a + 1) / 2 ^ 19 = a / 2 ^ 19 + 1 / 2 ^ 19 := by ring
    rw [e]
    linarith
  · rw [abs_of_pos (by linarith : (0 : ℝ) < T)]
    have k : T / 2 ^ 63 + 8 * T / 2 ^ 86 + 2 * T * (1 / 2 ^ 92 + 1 / 2 ^ 132) +
        2 * T * (1 / 2 ^ 99 + 1 / 2 ^ 139 + 1 / 2 ^ 179) + T / 2 ^ 1060 ≤ T / (2 ^ 53 + 1) := by
      have : T / (2 ^ 53 + 1) = T * (1 / (2 ^ 53 + 1)) := by ring
      rw [this]
      have h3 : (1 : ℝ) / 2 ^ 63 + 8 / 2 ^ 86 + 2 * (1 / 2 ^ 92 + 1 / 2 ^ 132) +
          2 * (1 / 2 ^ 99 + 1 / 2 ^ 139 + 1 / 2 ^ 179) + 1 / 2 ^ 1060 ≤ 1 / (2 ^ 53 + 1) := by
        norm_num
      have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ T)
      linarith
    have k1 : (a / 2 ^ 40 + a / 2 ^ 80) / 2 ^ 52 ≤ 2 * T * (1 / 2 ^ 92 + 1 / 2 ^ 132) := by
      have : (a / 2 ^ 40 + a / 2 ^ 80) / 2 ^ 52 = a * (1 / 2 ^ 92 + 1 / 2 ^ 132) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right haT (by positivity)
    have k2 : (a + a / 2 ^ 40 + a / 2 ^ 80) / 2 ^ 99 ≤
        2 * T * (1 / 2 ^ 99 + 1 / 2 ^ 139 + 1 / 2 ^ 179) := by
      have : (a + a / 2 ^ 40 + a / 2 ^ 80) / 2 ^ 99 = a * (1 / 2 ^ 99 + 1 / 2 ^ 139 + 1 / 2 ^ 179) := by
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_right haT (by positivity)
    have k3 : (1 : ℝ) / 2 ^ 1070 ≤ T / 2 ^ 1060 := by
      rw [le_div_iff₀ (by positivity)]
      calc (1 : ℝ) / 2 ^ 1070 * 2 ^ 1060 = 1 / 2 ^ 10 := by norm_num
        _ ≤ T := by linarith
    have k4 : y / 2 ^ 86 ≤ 8 * T / 2 ^ 86 := div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith

end Library.Numerics.Float64.Lgamma.LgammaAccPos
