import Verified.Examples.LgammaAccPos
import Verified.Examples.LgammaAccRegion
import Verified.Examples.LgammaAccCancel

/-!
**The triple of `Lgamma.accurate` at a negative argument**, through the reflection.  `NormReady`
collects the hypotheses of `LgammaAccPair.norm_pair` on the triple before the renormalization, and
`ready_pair` applies it; `pos_ready` covers the positive arguments.  From -21/2 to -1/4,
`NegSmall T r` states a triple within the error of the windows of `log Γ (1 + |x|)` with small
parts, and `small_ready` carries it through the reflection (`LgammaAccRefl.refl_spec`): the error
stays below `(1/20)/(2^53 + 1)`, and `LgammaAccRegion.neg_mid_lower` bounds `|log |Γ x||` by
`1/20` from below whenever no polynomial about a zero applies.
-/

namespace Verified.Examples.LgammaAccNeg
open CodeLib.IEEE64 LeanExe.ProofKit Tgamma TgammaDD LgammaAccTail LgammaAccWin LgammaLogAccKern
open Verified.Examples.Tgamma (floorF)

set_option exponentiation.threshold 4096

/-- The hypotheses of `norm_pair` on a triple. -/
def NormReady (L : ℝ) (sx : Float) (r : Float × Float × Float) : Prop :=
  ∃ A E B C : ℝ, Finite r.1.toBits ∧ Finite r.2.1.toBits ∧ Finite r.2.2.toBits ∧
    |value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits - L| ≤ E ∧
    |value r.1.toBits| ≤ A ∧ |value r.2.1.toBits| ≤ B ∧ |value r.2.2.toBits| ≤ C ∧
    A ≤ 2 ^ 850 ∧ B ≤ 2 ^ 840 ∧ C ≤ 2 ^ 800 ∧ B + C ≤ (|value r.1.toBits| + 1) / 2 ^ 19 ∧
    E + (B + C) / 2 ^ 52 + (A + B + C) / 2 ^ 99 + 1 / 2 ^ 1070 ≤ 1 / 2 ^ 50 + |L| / 2 ^ 50 ∧
    (∀ p1 : Float, Finite p1.toBits →
      (|value p1.toBits| < 3 / 8 → |value p1.toBits| ≤ |L| * (1 + 1 / 2 ^ 50) + 1 / 2 ^ 44) →
      (3 / 8 ≤ |value p1.toBits| → 1 / 4 ≤ |L|) →
      (|value p1.toBits| < 3 / 8 → Lgamma.rootRange p1.abs sx = (0, 0, 0, 0.0)) →
      E + (B + C) / 2 ^ 52 + (A + B + C) / 2 ^ 99 + 1 / 2 ^ 1070 ≤ |L| / (2 ^ 53 + 1))

/-- **The renormalized pair** of a triple with `NormReady`. -/
theorem ready_pair (L : ℝ) (sx a b c : Float) (hP : NormReady L sx (a, b, c))
    (h1 l1 : Float) (e1 : fastTwoSum a b = (h1, l1))
    (l2 ll2 : Float) (e2 : fastTwoSum l1 c = (l2, ll2))
    (h3 l3 : Float) (e3 : fastTwoSum h1 l2 = (h3, l3))
    (l4 ll4 : Float) (e4 : fastTwoSum l3 ll2 = (l4, ll4)) (cond : Bool) :
    AccPair L sx (if cond = true then
        (h3, l4 * (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) l4 *
          Lgamma.copySign (Float.ofBits 0x3E50000000000000) ll4))
      else (h3, l4)) := by
  obtain ⟨A, E, B, C, fa, fb, fc, hE, hA', hB', hC', hA, hB, hC, hBC, hEs, hbud⟩ := hP
  exact LgammaAccPair.norm_pair L sx a b c fa fb fc A E B C hE hA' hB' hC' hA hB hC hBC hEs
    hbud h1 l1 e1 l2 ll2 e2 h3 l3 e3 l4 ll4 e4 cond

/-- A positive argument's triple is ready for the renormalization. -/
theorem pos_ready (L : ℝ) (sx : Float) (r : Float × Float × Float)
    (hP : LgammaAccPos.PosSpec L r) : NormReady L sx r := by
  obtain ⟨A, E, B, C, fa, fb, fc, hE, hA', hB', hC', hA, hB, hC, hBC, hbud⟩ := hP
  have hL : |L| / (2 ^ 53 + 1) ≤ 1 / 2 ^ 50 + |L| / 2 ^ 50 := by
    have : |L| / (2 ^ 53 + 1) ≤ |L| / 2 ^ 50 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num)
    linarith [(by positivity : (0 : ℝ) ≤ 1 / 2 ^ 50)]
  exact ⟨A, E, B, C, fa, fb, fc, hE, hA', hB', hC', hA, hB, hC, hBC, hbud.trans hL,
    fun _ _ _ _ _ => hbud⟩

/-- The triple of `log Γ (1 + |x|)` from a window or Stirling's series below 21/2. -/
def NegSmall (T : ℝ) (r : Float × Float × Float) : Prop :=
  ∃ E Bl Bll : ℝ, Finite r.1.toBits ∧ Finite r.2.1.toBits ∧ Finite r.2.2.toBits ∧
    |value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits - T| ≤ E ∧
    |value r.1.toBits| ≤ 40 ∧ |value r.2.1.toBits| ≤ Bl ∧ |value r.2.2.toBits| ≤ Bll ∧
    E ≤ 9 / 2 ^ 61 + 1 / 2 ^ 69 + 1 / 2 ^ 84 ∧ Bl ≤ 1 / 2 ^ 34 ∧ Bll ≤ 1 / 2 ^ 60

/-- A window of `log Γ (1 + |x|)` gives `NegSmall`. -/
theorem win_small (T E B C : ℝ) (r : Float × Float × Float) (hw : WinSpec T E B C r)
    (hE : E ≤ 9 / 2 ^ 61 + 1 / 2 ^ 69 + 1 / 2 ^ 84) (hB : B ≤ 1 / 2 ^ 34) (hC : C ≤ 1 / 2 ^ 60) :
    NegSmall T r := by
  obtain ⟨f1, f2, f3, he, h4, hb, hc⟩ := hw
  exact ⟨E, B, C, f1, f2, f3, he, by linarith, hb, hc, hE, hB, hC⟩

set_option maxHeartbeats 4000000 in
/-- **The reflection from -21/2 to -1/4**: the reflected triple is ready for the
renormalization. -/
theorem small_ready (hF : FmaSpec.FmaNearest) (hS : LgammaApprox.SinpiFact)
    (hSA : LgammaApprox.SinpiAccFact) (hLA : LgammaApprox.LogAccFact) (sx : Float)
    (hsx : Finite sx.toBits) (hneg : value sx.toBits < 0) (hint : ∀ n : ℤ, value sx.toBits ≠ n)
    (h1 : -(21 / 2) < value sx.toBits) (hq : value sx.toBits ≤ -1 / 4)
    (fh fl fll : Float)
    (hP : NegSmall (GammaBasic.lgamma (1 + |value sx.toBits|)) (fh, fl, fll))
    (phi : Float) (hphi : phi = if sx < -0.5 then sx - floorF sx else -sx)
    (sh sl : Float) (hA : Lgamma.asSinpipidAccurate Lgamma.sinpiTable phi = (sh, sl))
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H sh = (lh, ll, lll))
    (ll2 : Float) (hll2 : ll2 = ll + (sl / sh + lll))
    (a1 b1 : Float) (hS1 : sumDD fl fll ll2 0.0 = (a1, b1))
    (h2 l2 : Float) (hP2 : twoSum fh lh = (h2, l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    NormReady (GammaBasic.lgamma (value sx.toBits)) sx (-h2, -a3, -b3) := by
  obtain ⟨E, Bl, Bll, f1, f2, f3, hE, hfh, hfl, hfll, hE', hBl, hBll⟩ := hP
  dsimp only at f1 f2 f3 hE hfh hfl hfll
  have hBl0 : 0 ≤ Bl := le_trans (abs_nonneg _) hfl
  have hBll0 : 0 ≤ Bll := le_trans (abs_nonneg _) hfll
  obtain ⟨n1, n2, n3, v1, v2, v3, herr, hh2, ha3, hb3⟩ := LgammaAccRefl.refl_spec hF hS hSA hLA
    sx hsx hneg hint hq (by linarith) fh fl fll f1 f2 f3 E Bl Bll hE (by linarith) hfl
    (by linarith) hfll (by linarith) phi hphi sh sl hA lh ll lll hT ll2 hll2 a1 b1 hS1 h2 l2 hP2
    a3 b3 hS3
  have hh2' : |value h2.toBits| ≤ 81 := by linarith
  have ha3' : |value a3.toBits| ≤ 1 / 2 ^ 33 := by
    have : |value h2.toBits| / 2 ^ 52 ≤ 81 / 2 ^ 52 := div_le_div_of_nonneg_right hh2' (by positivity)
    have k : (Bl + 1 / 2 ^ 40 + |value h2.toBits| / 2 ^ 52) * (1 + 1 / 2 ^ 49) ≤
        (1 / 2 ^ 34 + 1 / 2 ^ 40 + 81 / 2 ^ 52) * (1 + 1 / 2 ^ 49) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have k2 : (1 / 2 ^ 34 + 1 / 2 ^ 40 + 81 / 2 ^ 52) * (1 + 1 / 2 ^ 49) + 1 / 2 ^ 1070 ≤
        (1 : ℝ) / 2 ^ 33 := by norm_num
    linarith
  have hb3' : |value b3.toBits| ≤ 1 / 2 ^ 58 := by
    have k : (Bll + (Bl + 1 / 2 ^ 40) / 2 ^ 50) * (1 + 1 / 2 ^ 49) ≤
        (1 / 2 ^ 60 + (1 / 2 ^ 34 + 1 / 2 ^ 40) / 2 ^ 50) * (1 + 1 / 2 ^ 49) := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      have : (Bl + 1 / 2 ^ 40) / 2 ^ 50 ≤ (1 / 2 ^ 34 + 1 / 2 ^ 40) / 2 ^ 50 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      linarith
    have k2 : (1 / 2 ^ 60 + (1 / 2 ^ 34 + 1 / 2 ^ 40) / 2 ^ 50) * (1 + 1 / 2 ^ 49) +
        1 / 2 ^ 33 / 2 ^ 51 + 1 / 2 ^ 1070 ≤ (1 : ℝ) / 2 ^ 58 := by norm_num
    have : |value a3.toBits| / 2 ^ 51 ≤ 1 / 2 ^ 33 / 2 ^ 51 :=
      div_le_div_of_nonneg_right ha3' (by positivity)
    linarith
  have herr' : |value (-h2).toBits + value (-a3).toBits + value (-b3).toBits -
      GammaBasic.lgamma (value sx.toBits)| ≤ 9 / 2 ^ 61 + 1 / 2 ^ 68 := by
    refine herr.trans ?_
    have : |value h2.toBits| / 2 ^ 100 ≤ 81 / 2 ^ 100 := div_le_div_of_nonneg_right hh2' (by positivity)
    have k : (7 * Bll + (Bl + 1 / 2 ^ 40) / 2 ^ 47 + |value h2.toBits| / 2 ^ 100) / 2 ^ 53 ≤
        (7 / 2 ^ 60 + (1 / 2 ^ 34 + 1 / 2 ^ 40) / 2 ^ 47 + 81 / 2 ^ 100) / 2 ^ 53 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (Bl + 1 / 2 ^ 40) / 2 ^ 47 ≤ (1 / 2 ^ 34 + 1 / 2 ^ 40) / 2 ^ 47 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      linarith
    have k2 : 9 / 2 ^ 61 + 1 / 2 ^ 69 + 1 / 2 ^ 84 + 1 / 2 ^ 84 +
        ((7 / 2 ^ 60 + (1 / 2 ^ 34 + 1 / 2 ^ 40) / 2 ^ 47 + 81 / 2 ^ 100) / 2 ^ 53 + 1 / 2 ^ 1100) ≤
        (9 : ℝ) / 2 ^ 61 + 1 / 2 ^ 68 := by norm_num
    linarith
  have hEt : 9 / 2 ^ 61 + 1 / 2 ^ 68 + (1 / 2 ^ 33 + 1 / 2 ^ 58) / 2 ^ 52 +
      (81 + 1 / 2 ^ 33 + 1 / 2 ^ 58) / 2 ^ 99 + 1 / 2 ^ 1070 ≤ (1 / 20 : ℝ) / (2 ^ 53 + 1) := by
    norm_num
  refine ⟨81, 9 / 2 ^ 61 + 1 / 2 ^ 68, 1 / 2 ^ 33, 1 / 2 ^ 58, n1, n2, n3, herr',
    by dsimp only; rw [v1, abs_neg]; exact hh2', by dsimp only; rw [v2, abs_neg]; exact ha3',
    by dsimp only; rw [v3, abs_neg]; exact hb3', by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · dsimp only
    have : (0 : ℝ) ≤ |value (-h2).toBits| / 2 ^ 19 := by positivity
    have e : (|value (-h2).toBits| + 1) / 2 ^ 19 = |value (-h2).toBits| / 2 ^ 19 + 1 / 2 ^ 19 := by
      ring
    rw [e]
    have : (1 : ℝ) / 2 ^ 33 + 1 / 2 ^ 58 ≤ 1 / 2 ^ 19 := by norm_num
    linarith
  · have : (1 / 20 : ℝ) / (2 ^ 53 + 1) ≤ 1 / 2 ^ 50 := by norm_num
    have : (0 : ℝ) ≤ |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 50 := by positivity
    linarith
  · intro p1 hp1 hclose hfar hroot
    have hL := LgammaAccRegion.neg_mid_lower sx hsx hint h1 hq p1 hp1 hclose hfar hroot
    have : (1 / 20 : ℝ) / (2 ^ 53 + 1) ≤ |GammaBasic.lgamma (value sx.toBits)| / (2 ^ 53 + 1) :=
      div_le_div_of_nonneg_right hL (by positivity)
    linarith

end Verified.Examples.LgammaAccNeg
