import Verified.Examples.LgammaAccNegAsym

/-!
**Stirling's series at a negative argument from -21/2 down**, through the reflection.
`NegLarge T y r` states the bounds of `LgammaAsymAcc.asym_spec` on the triple of
`T = log Γ y` at `y = 1 + |x|`, the sharper one below 33 (`asym_large`).  The reflection cancels
by at most `2^32` from -21/2 to -32 (`LgammaApprox.CancelFact`) and by at most 2 below
(`LgammaAccCancel.cancel_double`), so the error of the reflected and renormalized pair stays below
`|log |Γ x||/(2^53 + 1)` (`large_ready`).
-/

namespace Verified.Examples.LgammaAccNegLarge
open CodeLib.IEEE64 LeanExe.ProofKit Tgamma TgammaDD LgammaAccWin LgammaLogAccKern LgammaAccNeg
open Real GammaBasic
open Verified.Examples.Tgamma (floorF)

set_option exponentiation.threshold 4096

/-- The triple of Stirling's series for `T = log Γ y`. -/
def NegLarge (T y : ℝ) (r : Float × Float × Float) : Prop :=
  Finite r.1.toBits ∧ Finite r.2.1.toBits ∧ Finite r.2.2.toBits ∧ 0 < value r.1.toBits ∧
    |value r.2.1.toBits| ≤ value r.1.toBits / 2 ^ 40 ∧
    |value r.2.2.toBits| ≤ value r.1.toBits / 2 ^ 80 ∧
    |value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits - T| ≤ T / 2 ^ 63 + y / 2 ^ 86 ∧
    (y < 33 → |value r.1.toBits + value r.2.1.toBits + value r.2.2.toBits - T| ≤
      T / 2 ^ 87 + y * (1 / 2 ^ 88 + 1 / 2 ^ 91))

set_option maxHeartbeats 4000000 in
/-- **The series from 21/2 to `2^800`.** -/
theorem asym_large (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAF : LgammaApprox.AsymFact) (x : Float) (hx : Finite x.toBits)
    (h1 : 21 / 2 ≤ value x.toBits) (h2 : value x.toBits ≤ 2 ^ 800) (xh xl : Float)
    (hT : fastTwoSum x 1.0 = (xh, xl)) :
    NegLarge (lgamma (1 + value x.toBits)) (1 + value x.toBits)
      (Lgamma.asLgammaAsymAccurate Tgamma.logdTable H Lgamma.asymTable xh xl) := by
  obtain ⟨fh, fl, hs, hlo, hhi, hlb, hl1, hxh2⟩ :=
    LgammaAccNegAsym.asym_input x hx (by linarith) h2 xh xl hT
  obtain ⟨f1, f2, f3, he, hr0, hb, hc⟩ := LgammaAsymAcc.asym_spec hF hLA hAF xh xl fh fl hlo hhi
    hlb hl1
  rw [hs, show value x.toBits + 1 = 1 + value x.toBits by ring] at he
  have hT0 := LgammaAccNegAsym.lgamma_nonneg (1 + value x.toBits) (by linarith)
  refine ⟨f1, f2, f3, hr0, hb, hc, he.trans ?_, fun h33 => he.trans ?_⟩
  · have k1 : (if value xh.toBits < 48 then (1 : ℝ) / 2 ^ 87 else 1 / 2 ^ 63) ≤ 1 / 2 ^ 63 := by
      split_ifs <;> norm_num
    have k2 : (if value xh.toBits < 2 ^ 120 then (1 : ℝ) / 2 ^ 88 + 1 / 2 ^ 91 else 1 / 2 ^ 86) ≤
        1 / 2 ^ 86 := by
      split_ifs <;> norm_num
    have := mul_le_mul_of_nonneg_right k1 hT0
    have := mul_le_mul_of_nonneg_left k2 (by linarith : (0 : ℝ) ≤ 1 + value x.toBits)
    linarith
  · have h48 : value xh.toBits < 48 := by linarith
    have h120 : value xh.toBits < 2 ^ 120 := by linarith [(by norm_num : (48 : ℝ) < 2 ^ 120)]
    rw [if_pos h48, if_pos h120]
    linarith

/-- `log Γ y ≤ 111` from 2 to 33: `Γ 33 = 32! ≤ 32^32 = 2^160`. -/
theorem lgamma_le_111 (y : ℝ) (h1 : 2 ≤ y) (h2 : y ≤ 33) : lgamma y ≤ 111 := by
  have hm := Gamma_strictMonoOn_Ici.monotoneOn (show y ∈ Set.Ici 2 by rw [Set.mem_Ici]; exact h1)
    (show (33 : ℝ) ∈ Set.Ici 2 by rw [Set.mem_Ici]; norm_num) h2
  have h33 : Gamma 33 = (Nat.factorial 32 : ℝ) := by
    rw [show (33 : ℝ) = (32 : ℕ) + 1 by norm_num, Gamma_nat_eq_factorial]
  have hf : (Nat.factorial 32 : ℝ) ≤ 2 ^ 160 := by
    have : Nat.factorial 32 ≤ 2 ^ 160 := by decide +kernel
    exact_mod_cast this
  have hpos : 0 < Gamma y := Gamma_pos_of_pos (by linarith)
  unfold lgamma
  have hl := Real.log_le_log hpos (hm.trans (show Gamma 33 ≤ 2 ^ 160 by rw [h33]; exact hf))
  rw [Real.log_pow] at hl
  have := Real.log_two_lt_d9
  push_cast at hl
  norm_num at this
  linarith

set_option maxHeartbeats 16000000 in
/-- **The reflection from -21/2 down**: the reflected triple of Stirling's series is ready for
the renormalization. -/
theorem large_ready (hF : FmaSpec.FmaNearest) (hS : LgammaApprox.SinpiFact)
    (hSA : LgammaApprox.SinpiAccFact) (hLA : LgammaApprox.LogAccFact)
    (hCF : LgammaApprox.CancelFact) (sx : Float) (hsx : Finite sx.toBits)
    (hint : ∀ n : ℤ, value sx.toBits ≠ n) (hlo : value sx.toBits ≤ -(21 / 2))
    (hhi : -2 ^ 800 ≤ value sx.toBits) (fh fl fll : Float)
    (hP : NegLarge (lgamma (1 + |value sx.toBits|)) (1 + |value sx.toBits|) (fh, fl, fll))
    (phi : Float) (hphi : phi = if sx < -0.5 then sx - floorF sx else -sx)
    (sh sl : Float) (hA : Lgamma.asSinpipidAccurate Lgamma.sinpiTable phi = (sh, sl))
    (lh ll lll : Float) (hT : Lgamma.asLogdAccurate Tgamma.logdTable H sh = (lh, ll, lll))
    (ll2 : Float) (hll2 : ll2 = ll + (sl / sh + lll))
    (a1 b1 : Float) (hS1 : sumDD fl fll ll2 0.0 = (a1, b1))
    (h2 l2 : Float) (hP2 : twoSum fh lh = (h2, l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    NormReady (lgamma (value sx.toBits)) sx (-h2, -a3, -b3) := by
  obtain ⟨f1, f2, f3, hr0, hb, hc, hE, hE33⟩ := hP
  dsimp only at f1 f2 f3 hr0 hb hc hE hE33
  have hneg : value sx.toBits < 0 := by linarith
  have hav : |value sx.toBits| = -value sx.toBits := abs_of_neg hneg
  have hy1 : 23 / 2 ≤ 1 + |value sx.toBits| := by rw [hav]; linarith
  have hy2 : 1 + |value sx.toBits| ≤ 2 ^ 802 := by
    rw [hav]; linarith [(by norm_num : (2 : ℝ) ^ 800 + 1 ≤ 2 ^ 802)]
  have hTy := LgammaAccGrowth.growth_large _ hy1
  have hTu := LgammaAccGrowth.lgamma_upper _ (by linarith) hy2
  have hcan : lgamma (1 + |value sx.toBits|) ≤ 2 ^ 32 * |lgamma (value sx.toBits)| := by
    have h := hCF sx.toBits hsx (by linarith) hint
    rw [show 1 - value sx.toBits = 1 + |value sx.toBits| by rw [hav]; ring,
      abs_of_nonneg (by linarith)] at h
    exact h
  -- the high part of the triple
  have hfh : value fh.toBits ≤ 2 * lgamma (1 + |value sx.toBits|) + 1 := by
    have k := abs_le.mp hE
    have kb := abs_le.mp hb
    have kc := abs_le.mp hc
    have : (1 + |value sx.toBits|) / 2 ^ 86 ≤ lgamma (1 + |value sx.toBits|) := by
      have : (1 + |value sx.toBits|) / 2 ^ 86 ≤ 1 + |value sx.toBits| :=
        div_le_self (by linarith) (by norm_num)
      linarith
    have : lgamma (1 + |value sx.toBits|) / 2 ^ 63 ≤ lgamma (1 + |value sx.toBits|) :=
      div_le_self (by linarith) (by norm_num)
    linarith
  have hfhb : |value fh.toBits| ≤ 2 ^ 840 := by
    rw [abs_of_pos hr0]; linarith [(by norm_num : (2 : ℝ) * 2 ^ 812 + 1 ≤ 2 ^ 840)]
  have hfh2 : value fh.toBits ≤ 2 * 2 ^ 812 + 1 := by linarith
  have hBl : value fh.toBits / 2 ^ 40 ≤ 2 ^ 830 :=
    (div_le_div_of_nonneg_right hfh2 (by positivity)).trans (by norm_num)
  have hBll : value fh.toBits / 2 ^ 80 ≤ 2 ^ 780 :=
    (div_le_div_of_nonneg_right hfh2 (by positivity)).trans (by norm_num)
  have hq : value sx.toBits ≤ -1 / 4 := by linarith
  have hbig : -2 ^ 52 < value sx.toBits := by
    by_contra h
    push Not at h
    exact hint (round (value sx.toBits)) (by
      obtain ⟨K, hK⟩ := LgammaRootPath.grid_p sx.toBits hsx 52 (by norm_num)
        (by rw [abs_of_neg hneg]; linarith)
      rw [hK, show (K : ℝ) * 2 ^ 52 / 2 ^ 52 = K by field_simp]
      simp)
  by_cases h33 : 1 + |value sx.toBits| < 33
  · -- from -21/2 to -32: the reflection loses at most `2^32`
    obtain ⟨n1, n2, n3, v1, v2, v3, herr, hh2, ha3, hb3⟩ := LgammaAccRefl.refl_spec hF hS hSA hLA
      sx hsx hneg hint hq hbig fh fl fll f1 f2 f3 _ _ _ (hE33 h33) hfhb hb hBl hc hBll phi hphi
      sh sl hA lh ll lll hT ll2 hll2 a1 b1 hS1 h2 l2 hP2 a3 b3 hS3
    have hT111 := lgamma_le_111 _ (by linarith) h33.le
    generalize lgamma (1 + |value sx.toBits|) = T at hTy hTu hcan hfh hT111 herr
    generalize 1 + |value sx.toBits| = y at hTy hy1 hy2 herr h33
    generalize lgamma (value sx.toBits) = L at hcan herr ⊢
    have hh2' : |value h2.toBits| ≤ 2 * T + 43 := by
      rw [abs_of_pos hr0] at hh2; linarith
    have ha3' : |value a3.toBits| ≤ (2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 39 := by
      have k1 : value fh.toBits / 2 ^ 40 ≤ (2 * T + 1) / 2 ^ 40 :=
        div_le_div_of_nonneg_right hfh (by positivity)
      have k2 : |value h2.toBits| / 2 ^ 52 ≤ 265 / 2 ^ 52 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have k3 := mul_le_mul_of_nonneg_right (show value fh.toBits / 2 ^ 40 + 1 / 2 ^ 40 +
        |value h2.toBits| / 2 ^ 52 ≤ (2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + 265 / 2 ^ 52 by linarith)
        (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 49)
      have k4 : (2 * T + 1) / 2 ^ 40 * (1 / 2 ^ 49) ≤ 223 / 2 ^ 89 := by
        rw [show (2 * T + 1) / 2 ^ 40 * (1 / 2 ^ 49) = (2 * T + 1) / 2 ^ 89 by ring]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      have k5 : ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + 265 / 2 ^ 52) * (1 + 1 / 2 ^ 49) =
          (2 * T + 1) / 2 ^ 40 + (2 * T + 1) / 2 ^ 40 * (1 / 2 ^ 49) +
            (1 / 2 ^ 40 + 265 / 2 ^ 52) * (1 + 1 / 2 ^ 49) := by ring
      have k6 : 223 / 2 ^ 89 + (1 / 2 ^ 40 + 265 / 2 ^ 52) * (1 + 1 / 2 ^ 49) + 1 / 2 ^ 1070 ≤
          (1 : ℝ) / 2 ^ 39 := by norm_num
      linarith
    have hb3' : |value b3.toBits| ≤ 1 / 2 ^ 60 := by
      have k1 : value fh.toBits / 2 ^ 80 ≤ 223 / 2 ^ 80 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have k2 : (value fh.toBits / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50 ≤ (223 / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50 :=
        div_le_div_of_nonneg_right (by
          have : value fh.toBits / 2 ^ 40 ≤ 223 / 2 ^ 40 :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
          linarith) (by positivity)
      have k3 := mul_le_mul_of_nonneg_right (show value fh.toBits / 2 ^ 80 +
        (value fh.toBits / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50 ≤
          223 / 2 ^ 80 + (223 / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50 by linarith)
        (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 49)
      have k4 : |value a3.toBits| / 2 ^ 51 ≤ (223 / 2 ^ 40 + 1 / 2 ^ 39) / 2 ^ 51 :=
        div_le_div_of_nonneg_right (by
          have : (2 * T + 1) / 2 ^ 40 ≤ 223 / 2 ^ 40 :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
          linarith) (by positivity)
      have k5 : (223 / 2 ^ 80 + (223 / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50) * (1 + 1 / 2 ^ 49) +
          (223 / 2 ^ 40 + 1 / 2 ^ 39) / 2 ^ 51 + 1 / 2 ^ 1070 ≤ (1 : ℝ) / 2 ^ 60 := by norm_num
      linarith
    -- the error of the reflected triple
    have herr' : |value (-h2).toBits + value (-a3).toBits + value (-b3).toBits - L| ≤
        (T / 2 ^ 87 + y * (1 / 2 ^ 88 + 1 / 2 ^ 91) + 1 / 2 ^ 84 + 1 / 2 ^ 120) := by
      refine herr.trans ?_
      have k1 : value fh.toBits / 2 ^ 80 ≤ 223 / 2 ^ 80 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have k2 : (value fh.toBits / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 ≤ (223 / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 :=
        div_le_div_of_nonneg_right (by
          have : value fh.toBits / 2 ^ 40 ≤ 223 / 2 ^ 40 :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
          linarith) (by positivity)
      have k3 : |value h2.toBits| / 2 ^ 100 ≤ 265 / 2 ^ 100 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have k4 : (7 * (value fh.toBits / 2 ^ 80) + (value fh.toBits / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 +
          |value h2.toBits| / 2 ^ 100) / 2 ^ 53 ≤
          (7 * (223 / 2 ^ 80) + (223 / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 + 265 / 2 ^ 100) / 2 ^ 53 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have k5 : (7 * (223 / 2 ^ 80) + (223 / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 + 265 / 2 ^ 100) / 2 ^ 53 +
          1 / 2 ^ 1100 ≤ (1 : ℝ) / 2 ^ 120 := by norm_num
      linarith
    have hL0 : T / 2 ^ 32 ≤ |L| := by
      rw [div_le_iff₀ (by positivity)]; linarith
    -- the budget, relative to `|L| ≥ T/2^32`
    have hbud : (T / 2 ^ 87 + y * (1 / 2 ^ 88 + 1 / 2 ^ 91) + 1 / 2 ^ 84 + 1 / 2 ^ 120) + ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 39 + 1 / 2 ^ 60) / 2 ^ 52 +
        (2 * T + 43 + ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 39) + 1 / 2 ^ 60) / 2 ^ 99 + 1 / 2 ^ 1070 ≤
        |L| / (2 ^ 53 + 1) := by
      have hT15 : 1495 / 100 ≤ T := by linarith
      have hyT : y ≤ 10 * T / 13 := by linarith
      have k : |L| / (2 ^ 53 + 1) ≥ T / 2 ^ 32 / (2 ^ 53 + 1) :=
        div_le_div_of_nonneg_right hL0 (by positivity)
      have k2 : y * (1 / 2 ^ 88 + 1 / 2 ^ 91) ≤ 10 * T / 13 * (1 / 2 ^ 88 + 1 / 2 ^ 91) :=
        mul_le_mul_of_nonneg_right hyT (by positivity)
      have k3 : (1 : ℝ) / 2 ^ 84 + 1 / 2 ^ 120 + 1 / 2 ^ 1070 ≤ T * (1 / 2 ^ 84 + 1 / 2 ^ 120 + 1 / 2 ^ 1070) / (1495 / 100) := by
        rw [le_div_iff₀ (by norm_num)]
        nlinarith
      have k4 : (1 / 2 ^ 87 + 10 / 13 * (1 / 2 ^ 88 + 1 / 2 ^ 91) + 2 / 2 ^ 92 + 2 / 2 ^ 99 + 2 / 2 ^ 139 +
          (1 / 2 ^ 84 + 1 / 2 ^ 120 + 1 / 2 ^ 1070) / (1495 / 100) +
          (1 / 2 ^ 92 + 1 / 2 ^ 91 + 1 / 2 ^ 112 + 44 / 2 ^ 99 + 1 / 2 ^ 139 + 1 / 2 ^ 138 + 1 / 2 ^ 159) / (1495 / 100)) ≤
          (1 : ℝ) / 2 ^ 32 / (2 ^ 53 + 1) := by norm_num
      have k5 := mul_le_mul_of_nonneg_left k4 (by linarith : (0 : ℝ) ≤ T)
      have k6 : (1 / 2 ^ 92 + 1 / 2 ^ 91 + 1 / 2 ^ 112 + 44 / 2 ^ 99 + 1 / 2 ^ 139 + 1 / 2 ^ 138 + 1 / 2 ^ 159 : ℝ) ≤
          T * ((1 / 2 ^ 92 + 1 / 2 ^ 91 + 1 / 2 ^ 112 + 44 / 2 ^ 99 + 1 / 2 ^ 139 + 1 / 2 ^ 138 + 1 / 2 ^ 159) / (1495 / 100)) := by
        rw [mul_div_assoc', le_div_iff₀ (by norm_num)]
        nlinarith
      have e : T / 2 ^ 32 / (2 ^ 53 + 1) = T * (1 / 2 ^ 32 / (2 ^ 53 + 1)) := by ring
      linarith
    refine ⟨2 * T + 43, (T / 2 ^ 87 + y * (1 / 2 ^ 88 + 1 / 2 ^ 91) + 1 / 2 ^ 84 + 1 / 2 ^ 120), (2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 39, 1 / 2 ^ 60, n1, n2, n3, herr',
      by dsimp only; rw [v1, abs_neg]; exact hh2', by dsimp only; rw [v2, abs_neg]; exact ha3',
      by dsimp only; rw [v3, abs_neg]; exact hb3', by linarith, by linarith, by norm_num, ?_, ?_,
      fun _ _ _ _ _ => hbud⟩
    · dsimp only
      have : (0 : ℝ) ≤ |value (-h2).toBits| / 2 ^ 19 := by positivity
      have e : (|value (-h2).toBits| + 1) / 2 ^ 19 = |value (-h2).toBits| / 2 ^ 19 + 1 / 2 ^ 19 := by
        ring
      rw [e]
      have k : (2 * T + 1) / 2 ^ 40 ≤ 223 / 2 ^ 40 := div_le_div_of_nonneg_right (by linarith)
        (by positivity)
      have : (223 : ℝ) / 2 ^ 40 + 1 / 2 ^ 39 + 1 / 2 ^ 60 ≤ 1 / 2 ^ 19 := by norm_num
      linarith
    · have : |L| / (2 ^ 53 + 1) ≤ 1 / 2 ^ 50 + |L| / 2 ^ 50 := by
        have : |L| / (2 ^ 53 + 1) ≤ |L| / 2 ^ 50 :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num)
        linarith [(by positivity : (0 : ℝ) ≤ 1 / 2 ^ 50)]
      linarith
  · -- from -32 down: the reflection loses at most 2
    have h32 : value sx.toBits ≤ -32 := by rw [hav] at h33; linarith
    obtain ⟨hc2, h69⟩ := LgammaAccCancel.cancel_double sx hsx h32 hint
    obtain ⟨n1, n2, n3, v1, v2, v3, herr, hh2, ha3, hb3⟩ := LgammaAccRefl.refl_spec hF hS hSA hLA
      sx hsx hneg hint hq hbig fh fl fll f1 f2 f3 _ _ _ hE hfhb hb hBl hc hBll phi hphi
      sh sl hA lh ll lll hT ll2 hll2 a1 b1 hS1 h2 l2 hP2 a3 b3 hS3
    generalize lgamma (1 + |value sx.toBits|) = T at hTy hTu hcan hfh herr hc2 h69
    generalize 1 + |value sx.toBits| = y at hTy hy1 hy2 herr h33
    generalize lgamma (value sx.toBits) = L at hcan herr hc2 ⊢
    have hfh0 : 0 ≤ value fh.toBits := hr0.le
    have hh2' : |value h2.toBits| ≤ 3 * T + 43 := by
      rw [abs_of_pos hr0] at hh2; linarith
    have kfl : value fh.toBits / 2 ^ 40 ≤ (2 * T + 1) / 2 ^ 40 :=
      div_le_div_of_nonneg_right hfh (by positivity)
    have kfll : value fh.toBits / 2 ^ 80 ≤ (2 * T + 1) / 2 ^ 80 :=
      div_le_div_of_nonneg_right hfh (by positivity)
    have kh52 : |value h2.toBits| / 2 ^ 52 ≤ (3 * T + 43) / 2 ^ 52 :=
      div_le_div_of_nonneg_right hh2' (by positivity)
    have kh100 : |value h2.toBits| / 2 ^ 100 ≤ (3 * T + 43) / 2 ^ 100 :=
      div_le_div_of_nonneg_right hh2' (by positivity)
    have ha3' : |value a3.toBits| ≤ (2 * ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + (3 * T + 43) / 2 ^ 52) + 1 / 2 ^ 1000) := by
      have X0 : 0 ≤ value fh.toBits / 2 ^ 40 + 1 / 2 ^ 40 + |value h2.toBits| / 2 ^ 52 := by positivity
      have k := mul_le_mul_of_nonneg_left (show (1 : ℝ) + 1 / 2 ^ 49 ≤ 2 by norm_num) X0
      linarith
    have hb3' : |value b3.toBits| ≤ (2 * ((2 * T + 1) / 2 ^ 80 + ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50) + (2 * ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + (3 * T + 43) / 2 ^ 52) + 1 / 2 ^ 1000) / 2 ^ 51 + 1 / 2 ^ 1000) := by
      have X0 : 0 ≤ value fh.toBits / 2 ^ 80 + (value fh.toBits / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50 := by
        positivity
      have k := mul_le_mul_of_nonneg_left (show (1 : ℝ) + 1 / 2 ^ 49 ≤ 2 by norm_num) X0
      have k2 : (value fh.toBits / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50 ≤
          ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have k3 : |value a3.toBits| / 2 ^ 51 ≤ (2 * ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + (3 * T + 43) / 2 ^ 52) + 1 / 2 ^ 1000) / 2 ^ 51 :=
        div_le_div_of_nonneg_right ha3' (by positivity)
      linarith
    have herr' : |value (-h2).toBits + value (-a3).toBits + value (-b3).toBits - L| ≤ (T / 2 ^ 63 + y / 2 ^ 86 + 1 / 2 ^ 84 + ((7 * ((2 * T + 1) / 2 ^ 80) + ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 + (3 * T + 43) / 2 ^ 100) / 2 ^ 53 + 1 / 2 ^ 1100)) := by
      refine herr.trans ?_
      have k : (7 * (value fh.toBits / 2 ^ 80) + (value fh.toBits / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 +
          |value h2.toBits| / 2 ^ 100) / 2 ^ 53 ≤
          (7 * ((2 * T + 1) / 2 ^ 80) + ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 +
            (3 * T + 43) / 2 ^ 100) / 2 ^ 53 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : (value fh.toBits / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 ≤
            ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        linarith
      linarith
    have hL2 : T ≤ 2 * |L| := hc2
    have hyT : y ≤ 10 * T / 13 := by linarith
    have hbud : (T / 2 ^ 63 + y / 2 ^ 86 + 1 / 2 ^ 84 + ((7 * ((2 * T + 1) / 2 ^ 80) + ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 + (3 * T + 43) / 2 ^ 100) / 2 ^ 53 + 1 / 2 ^ 1100)) + ((2 * ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + (3 * T + 43) / 2 ^ 52) + 1 / 2 ^ 1000) + (2 * ((2 * T + 1) / 2 ^ 80 + ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50) + (2 * ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + (3 * T + 43) / 2 ^ 52) + 1 / 2 ^ 1000) / 2 ^ 51 + 1 / 2 ^ 1000)) / 2 ^ 52 + (3 * T + 43 + (2 * ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + (3 * T + 43) / 2 ^ 52) + 1 / 2 ^ 1000) + (2 * ((2 * T + 1) / 2 ^ 80 + ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50) + (2 * ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + (3 * T + 43) / 2 ^ 52) + 1 / 2 ^ 1000) / 2 ^ 51 + 1 / 2 ^ 1000)) / 2 ^ 99 + 1 / 2 ^ 1070 ≤
        |L| / (2 ^ 53 + 1) := by
      have k : T / 2 / (2 ^ 53 + 1) ≤ |L| / (2 ^ 53 + 1) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have e : T / 2 / (2 ^ 53 + 1) = T * (1 / 2 / (2 ^ 53 + 1)) := by ring
      linarith
    -- `|L|` against the parts, for the bound on the low parts
    have hLh : |L| ≤ |value h2.toBits| + (2 * ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + (3 * T + 43) / 2 ^ 52) + 1 / 2 ^ 1000) + (2 * ((2 * T + 1) / 2 ^ 80 + ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50) + (2 * ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + (3 * T + 43) / 2 ^ 52) + 1 / 2 ^ 1000) / 2 ^ 51 + 1 / 2 ^ 1000) + (T / 2 ^ 63 + y / 2 ^ 86 + 1 / 2 ^ 84 + ((7 * ((2 * T + 1) / 2 ^ 80) + ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 + (3 * T + 43) / 2 ^ 100) / 2 ^ 53 + 1 / 2 ^ 1100)) := by
      have k := abs_sub_abs_le_abs_sub L (value (-h2).toBits + value (-a3).toBits + value (-b3).toBits)
      rw [abs_sub_comm] at k
      have k1 := abs_add_le (value (-h2).toBits + value (-a3).toBits) (value (-b3).toBits)
      have k2 := abs_add_le (value (-h2).toBits) (value (-a3).toBits)
      simp only [v1, v2, v3, abs_neg] at k1 k2
      rw [v1, v2, v3] at k herr'
      linarith
    refine ⟨3 * T + 43, (T / 2 ^ 63 + y / 2 ^ 86 + 1 / 2 ^ 84 + ((7 * ((2 * T + 1) / 2 ^ 80) + ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 47 + (3 * T + 43) / 2 ^ 100) / 2 ^ 53 + 1 / 2 ^ 1100)), (2 * ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + (3 * T + 43) / 2 ^ 52) + 1 / 2 ^ 1000), (2 * ((2 * T + 1) / 2 ^ 80 + ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40) / 2 ^ 50) + (2 * ((2 * T + 1) / 2 ^ 40 + 1 / 2 ^ 40 + (3 * T + 43) / 2 ^ 52) + 1 / 2 ^ 1000) / 2 ^ 51 + 1 / 2 ^ 1000), n1, n2, n3, herr',
      by dsimp only; rw [v1, abs_neg]; exact hh2', by dsimp only; rw [v2, abs_neg]; exact ha3',
      by dsimp only; rw [v3, abs_neg]; exact hb3', by linarith, by linarith, by linarith, ?_, ?_,
      fun _ _ _ _ _ => hbud⟩
    · dsimp only
      rw [v1, abs_neg]
      have e : (|value h2.toBits| + 1) / 2 ^ 19 = |value h2.toBits| / 2 ^ 19 + 1 / 2 ^ 19 := by ring
      rw [e]
      linarith
    · have : |L| / (2 ^ 53 + 1) ≤ 1 / 2 ^ 50 + |L| / 2 ^ 50 := by
        have : |L| / (2 ^ 53 + 1) ≤ |L| / 2 ^ 50 :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num)
        linarith [(by positivity : (0 : ℝ) ≤ 1 / 2 ^ 50)]
      linarith

end Verified.Examples.LgammaAccNegLarge
