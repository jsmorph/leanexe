import Verified.Examples.LgammaStir
import Verified.Examples.TgammaDDTop
import Verified.Examples.LgammaFastPos
import LeanExe.ProofKit.GammaThresholds

/-!
The fast path's Stirling series of `Lgamma.lgammaWith` from `2^800` to the overflow threshold of
`lgamma`.  The code forms `x (log x - 1)` with `mulDDD` from a pair `(p1, p2)` near `log x - 1`,
subtracts `p1/2`, adds the constant `c397 + c398` (`fastSum`), and adds the series term, which is
zero from `2^100` on (`fastSum`).  `stir_top_core` bounds the result as `LgammaStir.stir_b` does
below `2^800`, given a bound `H ≤ 2^1024 - 13 · 2^968` on `p1 x`, with the lemmas of
`TgammaDDTop`: the product near the threshold rounds within `H/2^53`, and the constant and the
zero are small addends, so the sums stay below the threshold.
-/

namespace Verified.Examples.LgammaStirTop
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPolyDDD TgammaExpr TgammaWords
  LgammaPiecePoly LgammaFastSmall LgammaFastMid LgammaStirSeries LgammaStir TgammaDDTop

set_option exponentiation.threshold 4096

/-- A finite double lies at most `2^1024 - 2^971` in magnitude. -/
theorem abs_le_max (w : UInt64) (hw : Finite w) : |value w| ≤ 2 ^ 1024 - 2 ^ 971 := by
  rw [← F64UpperWord.value_abs]
  have hl : (Wasm.IEEE64.abs w).toNat < F64NearestNonnegative.limit := by
    apply F64Magnitude.lt_limit_of_finite _ _ (F64Sign.fields_abs w).2.2
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hw ⊢
    rw [(F64Sign.fields_abs w).1]
    exact hw
  have hlim : F64NearestNonnegative.limit < 2 ^ 63 := by decide
  have hle := (F64PositiveOrder.value_le_iff (hl.trans hlim)
    (by decide : (0x7FEFFFFFFFFFFFFF : UInt64).toNat < 2 ^ 63)).mpr (by
      change (Wasm.IEEE64.abs w).toNat < 0x7FF0000000000000 at hl
      change (Wasm.IEEE64.abs w).toNat ≤ 0x7FEFFFFFFFFFFFFF
      omega)
  rw [F64PositiveRounding.largest_finite_value] at hle
  exact hle

set_option maxHeartbeats 2000000 in
/-- **The Stirling series from `2^800` to the threshold**, from a pair `(p1, p2)` within `2^-66`
of `log x - 1` and a bound `H` on `p1 x` below the threshold. -/
theorem stir_top_core (hF : FmaSpec.FmaNearest) (hSF : LgammaApprox.StirlingFact) (ax : Float)
    (hax : Finite ax.toBits) (h800 : 2 ^ 800 ≤ value ax.toBits)
    (hvx : value ax.toBits ≤ 2 ^ 1015) (p1 p2 : Float) (hp1 : Finite p1.toBits)
    (hp2 : Finite p2.toBits)
    (hP : |value p1.toBits + value p2.toBits - (Real.log (value ax.toBits) - 1)| ≤ 1 / 2 ^ 66)
    (hp2b : |value p2.toBits| ≤ 1 / 2 ^ 21) (H : ℝ)
    (hH : value p1.toBits * value ax.toBits ≤ H) (hHv : H ≤ 710 * value ax.toBits)
    (hHmax : H ≤ 2 ^ 1024 - 13 * 2 ^ 968)
    (M N R : Float × Float)
    (hM : M = ((mulDDD ax p1 p2).1, (mulDDD ax p1 p2).2 - p1 * 0.5))
    (hN : N = fastSum M.1 M.2 (entry Lgamma.mainTable 397) (entry Lgamma.mainTable 398))
    (hR : R = fastSum N.1 N.2 0.0 0.0) :
    Finite R.1.toBits ∧ Finite R.2.toBits ∧ 8 ≤ value R.1.toBits ∧
      |value R.2.toBits| ≤ value R.1.toBits / 2 ^ 17 ∧
      value R.1.toBits ≤ 2 ^ 1024 - 2 ^ 971 ∧
      |GammaBasic.lgamma (value ax.toBits) - (value R.1.toBits + value R.2.toBits)| +
          value R.1.toBits / 2 ^ 67 ≤
        2 * (value R.1.toBits * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)) -
          value R.1.toBits / 2 ^ 100 := by
  set v := value ax.toBits with hvdef
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) h800
  have hl2a : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2b : Real.log 2 < 0.6932 := by have := Real.log_two_lt_d9; linarith
  have hg1 : (554 : ℝ) ≤ Real.log v := by
    have h1 := Real.log_le_log (by positivity) h800
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hg2 : Real.log v ≤ 704 := by
    have h1 := Real.log_le_log hv0 hvx
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  set g := Real.log v with hgdef
  set lm := value p1.toBits with hlmdef
  set ll := value p2.toBits with hlldef
  have hlm1 : 552 ≤ lm := by
    have := abs_le.mp hP; have := abs_le.mp hp2b; linarith
  have hlm2 : lm ≤ 704 := by
    have := abs_le.mp hP; have := abs_le.mp hp2b; linarith
  -- `M = x (lm + ll)`
  have hH' : |lm| * |v| ≤ H := by
    rw [abs_of_pos hv0, abs_of_pos (by linarith)]
    exact hH
  have hLw : |ll| * |v| ≤ 1 / 2 ^ 21 * v := by
    rw [abs_of_pos hv0]
    exact mul_le_mul_of_nonneg_right hp2b hv0.le
  have hHlo : 552 * v ≤ H := by nlinarith
  have hHhi : H < 2 ^ 1024 := by linarith [(by norm_num : (0 : ℝ) < 13 * 2 ^ 968)]
  obtain ⟨hm1, hm2, hm3, hm4, hm5⟩ := mulDDD_spec_top hF ax p1 p2 hax hp1 hp2
    H (1 / 2 ^ 21 * v) hH' hLw (by linarith [(by norm_num : (0 : ℝ) < 2 ^ 970)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 21 * 2 ^ 1015 ≤ 2 ^ 1000)])
  set a := (mulDDD ax p1 p2).1 with hadef
  set b := (mulDDD ax p1 p2).2 with hbdef
  have k70 : 1 / 2 ^ 1071 ≤ v / 2 ^ 70 := by
    have : (2 : ℝ) ^ 800 / 2 ^ 70 ≤ v / 2 ^ 70 := div_le_div_of_nonneg_right h800 (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1071 ≤ 2 ^ 800 / 2 ^ 70)]
  have hH51 : H / 2 ^ 51 ≤ 710 * v / 2 ^ 51 := div_le_div_of_nonneg_right hHv (by norm_num)
  have hH52 : H / 2 ^ 52 ≤ 710 * v / 2 ^ 52 := div_le_div_of_nonneg_right hHv (by norm_num)
  have hM2 : |value b.toBits| ≤ v / 2 ^ 20 := by
    have : 1 / 2 ^ 21 * v * (1 + 1 / 2 ^ 51) ≤ v / 2 ^ 21 * (1 + 1 / 2 ^ 51) := le_of_eq (by ring)
    linarith
  have hprod : v * (g - 1 - 1 / 2 ^ 66) ≤ v * (lm + ll) := by
    apply mul_le_mul_of_nonneg_left _ hv0.le
    have := abs_le.mp hP; linarith
  have hM1lo : 550 * v ≤ value a.toBits := by
    have := abs_le.mp hm3
    have := abs_le.mp hM2
    nlinarith
  have hM1hi : value a.toBits ≤ H * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 := (abs_le.mp hm5).2
  -- `hl = lm/2` and `b - hl`
  have hhalf : (0.5 : Float).toBits = 0x3FE0000000000000 := rfl
  have hhf : Finite (0.5 : Float).toBits := by
    rw [hhalf]; unfold CodeLib.IEEE64.Finite; decide
  have hhv : value (0.5 : Float).toBits = 1 / 2 := by
    rw [hhalf, word_value _ (1 / 2) (by decide +kernel)]; norm_num
  have hh := fapprox_mul (fapprox_self _ hp1) (fapprox_self _ hhf) 704 (1 / 2)
    (by rw [abs_of_pos (by linarith)]; exact hlm2) (by rw [hhv]; norm_num) (704 * (1 / 2))
    (by norm_num) (by norm_num)
  rw [hhv] at hh
  set hl := p1 * 0.5 with hhldef
  have hhe : |value hl.toBits - lm * (1 / 2)| ≤ 1 / 2 ^ 44 := by
    have := hh.2
    norm_num at this ⊢
    linarith
  have hhb : |value hl.toBits| ≤ 353 := by
    have := abs_le.mp hhe; rw [abs_le]; constructor <;> linarith
  have h353 : (353 : ℝ) ≤ v / 2 ^ 20 := by
    have : (2 : ℝ) ^ 800 / 2 ^ 20 ≤ v / 2 ^ 20 := div_le_div_of_nonneg_right h800 (by norm_num)
    linarith [(by norm_num : (353 : ℝ) ≤ 2 ^ 800 / 2 ^ 20)]
  have hd := fapprox_sub (fapprox_self _ hm2) (fapprox_self _ hh.1) (v / 2 ^ 19)
    (by
      have := abs_sub (value b.toBits) (value hl.toBits)
      norm_num
      linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 1015 / 2 ^ 19 < 2 ^ 1023)])
  set m2 := b - hl with hm2def
  have hde : |value m2.toBits - (value b.toBits - value hl.toBits)| ≤ v / 2 ^ 72 := by
    have := hd.2; norm_num at this ⊢; linarith
  have hm2b : |value m2.toBits| ≤ v / 2 ^ 18 := by
    have h1 := abs_sub_abs_le_abs_sub (value m2.toBits) (value b.toBits - value hl.toBits)
    have := abs_sub (value b.toBits) (value hl.toBits)
    linarith
  -- `N = M + c`
  obtain ⟨hw397, hw398⟩ : Wasm.IEEE64.isFinite (wq 397) = true ∧
      Wasm.IEEE64.isFinite (wq 398) = true := ⟨coef_ok.1 0 (by norm_num), coef_ok.1 1 (by norm_num)⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, h397a, h397b, h398⟩ := coef_ok
  have hc397a := qcast_le h397a
  have hc397b := qcast_le h397b
  have hc398 := abs_rat_le _ _ h398
  push_cast at hc397a hc397b hc398
  have he397 : entry Lgamma.mainTable 397 = Float.ofBits (wq 397) := rfl
  have he398 : entry Lgamma.mainTable 398 = Float.ofBits (wq 398) := rfl
  rw [he397, he398] at hN
  have hv397 := ofBits_value _ hw397
  have hv398 := ofBits_value _ hw398
  rw [hM] at hN
  simp only [] at hN
  have hx8 : 2 ^ 800 ≤ |value a.toBits| := by
    rw [abs_of_pos (by linarith)]
    linarith [(by norm_num : (2 : ℝ) ^ 800 ≤ 550 * 2 ^ 800)]
  have hsum1 : |value a.toBits + value (Float.ofBits (wq 397)).toBits| < 2 ^ 1024 - 2 ^ 970 := by
    rw [hv397, abs_of_pos (by linarith)]
    have : H * (1 + 1 / 2 ^ 53) ≤ H + 2 ^ 1024 / 2 ^ 53 := by
      have : H / 2 ^ 53 ≤ 2 ^ 1024 / 2 ^ 53 := div_le_div_of_nonneg_right hHhi.le (by norm_num)
      linarith
    linarith [(by norm_num : (2 : ℝ) ^ 1024 - 13 * 2 ^ 968 + 2 ^ 1024 / 2 ^ 53 + 1 / 2 ^ 1075 + 1
      < 2 ^ 1024 - 2 ^ 970)]
  obtain ⟨hn1, hn2, hn3, hn4⟩ := fastSum_spec_small a m2 (Float.ofBits (wq 397))
    (Float.ofBits (wq 398)) hm1 hd.1 (ofBits_finite _ hw397) (ofBits_finite _ hw398)
    (by rw [hv397, abs_of_pos (by linarith)]; linarith) hx8 hsum1
    (v / 2 ^ 18 + 1 / 2 ^ 57) (by rw [hv398]; linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 1015 / 2 ^ 18 + 1 / 2 ^ 57 ≤ 2 ^ 1000)])
  rw [← hN] at hn1 hn2 hn3 hn4
  rw [hv397, hv398] at hn3
  set n1 := value N.1.toBits with hn1def
  set n2 := value N.2.toBits with hn2def
  have hNs : |n1| ≤ |n1 + n2| + |n2| := by
    have := abs_sub (n1 + n2) n2
    rwa [add_sub_cancel_right] at this
  have hHa : H * (1 + 1 / 2 ^ 53) ≤ 710 * v + 710 * v / 2 ^ 53 := by
    have : H / 2 ^ 53 ≤ 710 * v / 2 ^ 53 := div_le_div_of_nonneg_right hHv (by norm_num)
    linarith
  have hNm : |n1 + n2| ≤ 710 * v + 710 * v / 2 ^ 53 + 1 / 2 ^ 1075 + v / 2 ^ 18 + 42 / 100 +
      1 / 2 ^ 57 + (3 * (v / 2 ^ 18 + 1 / 2 ^ 57) + |n1| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by
    have h1 := abs_sub_abs_le_abs_sub (n1 + n2) (value a.toBits + value m2.toBits +
      (((PolyBound.ratOfWord (wq 397) : ℚ) : ℝ) + ((PolyBound.ratOfWord (wq 398) : ℚ) : ℝ)))
    have h2 := abs_add_le (value a.toBits + value m2.toBits)
      (((PolyBound.ratOfWord (wq 397) : ℚ) : ℝ) + ((PolyBound.ratOfWord (wq 398) : ℚ) : ℝ))
    have h3 := abs_add_le (value a.toBits) (value m2.toBits)
    have h4 := abs_add_le ((PolyBound.ratOfWord (wq 397) : ℚ) : ℝ)
      ((PolyBound.ratOfWord (wq 398) : ℚ) : ℝ)
    rw [abs_of_pos (by linarith : (0 : ℝ) < value a.toBits),
      abs_of_pos (show (0 : ℝ) < ((PolyBound.ratOfWord (wq 397) : ℚ) : ℝ) by linarith)] at *
    linarith
  have hN1b : |n1| ≤ 711 * v := by
    have : 1 / 2 ^ 1073 ≤ v / 2 ^ 70 := by
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1073 ≤ 1 / 2 ^ 1071)]
    linarith
  have hN2b : |n2| ≤ v / 2 ^ 17 := by
    have : |n1| / 2 ^ 51 ≤ 711 * v / 2 ^ 51 := div_le_div_of_nonneg_right hN1b (by norm_num)
    linarith
  have hN1lo : 549 * v ≤ n1 := by
    have := abs_le.mp hn3
    have := abs_le.mp hN2b
    have : |n1| / 2 ^ 52 ≤ 711 * v / 2 ^ 52 := div_le_div_of_nonneg_right hN1b (by norm_num)
    have := abs_le.mp hm2b
    have := abs_le.mp hc398
    linarith
  -- `R = N + 0`
  have hz : Finite (0.0 : Float).toBits := LgammaSpecial.zero_finite
  have hzv : value (0.0 : Float).toBits = 0 := by
    rw [TgammaSpecial.zero_bits, F64Magnitude.value_zero]
  have hN1max := abs_le_max N.1.toBits hn1
  obtain ⟨hr1, hr2, hr3, hr4⟩ := fastSum_spec_small N.1 N.2 0.0 0.0 hn1 hn2 hz hz
    (by rw [hzv, abs_zero]; norm_num)
    (by rw [abs_of_pos (by linarith : (0 : ℝ) < n1)]
        linarith [(by norm_num : (2 : ℝ) ^ 800 ≤ 549 * 2 ^ 800)])
    (by rw [hzv, add_zero]
        linarith [(by norm_num : (2 : ℝ) ^ 1024 - 2 ^ 971 < 2 ^ 1024 - 2 ^ 970)])
    (v / 2 ^ 17) (by rw [hzv, abs_zero, add_zero]; exact hN2b)
    (by linarith [(by norm_num : (2 : ℝ) ^ 1015 / 2 ^ 17 ≤ 2 ^ 1000)])
  rw [← hR] at hr1 hr2 hr3 hr4
  rw [hzv] at hr3
  set r1 := value R.1.toBits with hr1def
  set r2 := value R.2.toBits with hr2def
  have hRs : |r1| ≤ |r1 + r2| + |r2| := by
    have := abs_sub (r1 + r2) r2
    rwa [add_sub_cancel_right] at this
  have hRm : |r1 + r2| ≤ 711 * v + v / 2 ^ 17 +
      (3 * (v / 2 ^ 17) + |r1| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by
    have h1 := abs_sub_abs_le_abs_sub (r1 + r2) (n1 + n2 + (0 + 0))
    have h3 := abs_add_le n1 n2
    simp only [add_zero] at h1 hr3
    linarith
  have hR1b : |r1| ≤ 712 * v := by
    have : 1 / 2 ^ 1073 ≤ v / 2 ^ 70 := by
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1073 ≤ 1 / 2 ^ 1071)]
    linarith
  have hR2b : |r2| ≤ v / 2 ^ 16 := by
    have : |r1| / 2 ^ 51 ≤ 712 * v / 2 ^ 51 := div_le_div_of_nonneg_right hR1b (by norm_num)
    linarith
  have hR1lo : 548 * v ≤ r1 := by
    have := abs_le.mp hr3; have := abs_le.mp hN2b; have := abs_le.mp hR2b
    have : |r1| / 2 ^ 52 ≤ 712 * v / 2 ^ 52 := div_le_div_of_nonneg_right hR1b (by norm_num)
    simp only [add_zero] at *
    linarith
  -- the error against `stirFast`
  have hS := stirFast_eq v
  rw [show ((((PolyBound.ratOfWord (wq 399) + PolyBound.ratOfWord (wq 400) : ℚ)) : ℝ) +
    evalR sE ((1 / v) ^ 2)) * (1 / v) = Tx v from rfl] at hS
  have hTe := T_zero v (by linarith [(by norm_num : (2 : ℝ) ^ 100 ≤ 2 ^ 800)])
  rw [hzv] at hTe
  set c := ((PolyBound.ratOfWord (wq 397) + PolyBound.ratOfWord (wq 398) : ℚ) : ℝ) with hcdef
  have hc : c = ((PolyBound.ratOfWord (wq 397) : ℚ) : ℝ) +
      ((PolyBound.ratOfWord (wq 398) : ℚ) : ℝ) := by
    rw [hcdef]; push_cast; ring
  have hD : |v * (lm + ll) - lm * (1 / 2) - (v - 1 / 2) * (g - 1)| ≤ v / 2 ^ 66 + 1 / 2 ^ 20 := by
    rw [show v * (lm + ll) - lm * (1 / 2) - (v - 1 / 2) * (g - 1) =
      v * (lm + ll - (g - 1)) - (lm - (g - 1)) / 2 by ring]
    have e1 : |v * (lm + ll - (g - 1))| ≤ v / 2 ^ 66 := by
      rw [abs_mul, abs_of_pos hv0]
      calc v * |lm + ll - (g - 1)| ≤ v * (1 / 2 ^ 66) := mul_le_mul_of_nonneg_left hP hv0.le
        _ = v / 2 ^ 66 := by ring
    have e2 : |(lm - (g - 1)) / 2| ≤ 1 / 2 ^ 20 := by
      rw [abs_div, abs_two]
      have := abs_sub_abs_le_abs_sub (lm - (g - 1)) (-ll)
      rw [show lm - (g - 1) - -ll = lm + ll - (g - 1) by ring, abs_neg] at this
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 66 + 1 / 2 ^ 21 ≤ 2 / 2 ^ 20)]
    have := abs_sub (v * (lm + ll - (g - 1))) ((lm - (g - 1)) / 2)
    linarith
  have hE : |LgammaApprox.stirFast v - (r1 + r2)| ≤ v / 2 ^ 65 + 1 / 2 ^ 19 := by
    rw [hS, hc]
    have e1 := abs_le.mp hm3
    have e2 := abs_le.mp hn3
    have e3 := abs_le.mp hr3
    have e4 := abs_le.mp hTe
    have e5 := abs_le.mp hD
    have e6 := abs_le.mp hhe
    have e7 := abs_le.mp hde
    have f1 : |n1| / 2 ^ 52 ≤ 711 * v / 2 ^ 52 := div_le_div_of_nonneg_right hN1b (by norm_num)
    have f2 : |r1| / 2 ^ 52 ≤ 712 * v / 2 ^ 52 := div_le_div_of_nonneg_right hR1b (by norm_num)
    simp only [add_zero] at e3 e4
    rw [abs_le]
    constructor <;> linarith
  -- `StirlingFact`
  have hsf := hSF v (by
    have := qcast_le border19_hi; push_cast at this
    linarith [(by norm_num : (9 : ℝ) ≤ 2 ^ 800)])
  set L := GammaBasic.lgamma v with hLdef
  have hc5 := qcast_le c5_bounds.1
  push_cast at hc5
  have hR1c : r1 * (449 / 10 ^ 22) ≤ r1 * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hc5 (by linarith)
  have hR2r : |r2| ≤ r1 / 2 ^ 17 := by
    have : v / 2 ^ 16 ≤ 548 * v / 2 ^ 17 := by linarith
    have : 548 * v / 2 ^ 17 ≤ r1 / 2 ^ 17 := div_le_div_of_nonneg_right hR1lo (by norm_num)
    linarith
  have hR1top : r1 ≤ 2 ^ 1024 - 2 ^ 971 := le_trans (le_abs_self r1) (abs_le_max _ hr1)
  refine ⟨hr1, hr2, by linarith [(by norm_num : (8 : ℝ) ≤ 548 * 2 ^ 800)], hR2r, hR1top, ?_⟩
  have hLpos : 0 ≤ L := by
    have h0 : 0 ≤ 7 / 10 ^ 20 * L := (abs_nonneg _).trans hsf
    linarith
  have hLS : L ≤ LgammaApprox.stirFast v + 7 / 10 ^ 20 * L := by
    have := abs_le.mp hsf; linarith
  have hSR : LgammaApprox.stirFast v ≤ r1 * (1 + 1 / 2 ^ 16) := by
    have := abs_le.mp hE
    have := abs_le.mp hR2b
    have : v / 2 ^ 16 ≤ 548 * v / 2 ^ 25 := by linarith
    have : 548 * v / 2 ^ 25 ≤ r1 / 2 ^ 25 := div_le_div_of_nonneg_right hR1lo (by norm_num)
    have : v / 2 ^ 65 ≤ 548 * v / 2 ^ 74 := by linarith
    have : 548 * v / 2 ^ 74 ≤ r1 / 2 ^ 74 := div_le_div_of_nonneg_right hR1lo (by norm_num)
    have : 1 / 2 ^ 19 ≤ r1 / 2 ^ 70 := by
      have : 548 * (2 : ℝ) ^ 800 / 2 ^ 70 ≤ r1 / 2 ^ 70 :=
        div_le_div_of_nonneg_right (by linarith) (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 19 ≤ 548 * 2 ^ 800 / 2 ^ 70)]
    linarith
  have hfin : |L - (r1 + r2)| ≤ 7 / 10 ^ 20 * L + (v / 2 ^ 65 + 1 / 2 ^ 19) := by
    have := abs_sub_le L (LgammaApprox.stirFast v) (r1 + r2)
    linarith
  have hvr : v / 2 ^ 65 ≤ r1 / 548 / 2 ^ 65 := by
    have : v ≤ r1 / 548 := by linarith
    exact div_le_div_of_nonneg_right this (by norm_num)
  have h19 : 1 / 2 ^ 19 ≤ r1 / 2 ^ 70 := by
    have : 548 * (2 : ℝ) ^ 800 / 2 ^ 70 ≤ r1 / 2 ^ 70 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 19 ≤ 548 * 2 ^ 800 / 2 ^ 70)]
  linarith

/-- `eps = |r| · 4.5 · 10^-20` up to `2^1024`, as `LgammaFastPos.eps5_value` below `2^900`. -/
theorem eps5_value_top (r : Float) (hr : Finite r.toBits) (hrb : |value r.toBits| ≤ 2 ^ 1024) :
    Finite (r.abs * Float.ofBits 0x3BEA90352E248A68).toBits ∧
      |value (r.abs * Float.ofBits 0x3BEA90352E248A68).toBits -
        |value r.toBits| * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)| ≤
        |value r.toBits| * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ) / 2 ^ 53 +
          1 / 2 ^ 1075 := by
  obtain ⟨haf, hav⟩ := SinhWords.abs_float r hr
  have hw : Wasm.IEEE64.isFinite 0x3BEA90352E248A68 = true := by decide
  have hc5 := qcast_le LgammaStir.c5_bounds.1
  have hc5' := qcast_le LgammaStir.c5_bounds.2
  push_cast at hc5 hc5'
  have ha := fapprox_self r.abs haf
  have hb := fapprox_self (Float.ofBits 0x3BEA90352E248A68) (ofBits_finite _ hw)
  rw [hav] at ha
  rw [ofBits_value _ hw] at hb
  have hca : |((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)| =
      ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ) := abs_of_pos (by linarith)
  have hm := fapprox_mul ha hb (|value r.toBits|) ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)
    (by rw [abs_abs]) (le_of_eq hca)
    (|value r.toBits| * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)) (by simp)
    (by
      have : |value r.toBits| * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ) ≤
          2 ^ 1024 * (1 / 2 ^ 64) := mul_le_mul hrb hc5' (by linarith) (by norm_num)
      linarith [(by norm_num : (2 : ℝ) ^ 1024 * (1 / 2 ^ 64) < 2 ^ 1022)])
  refine ⟨hm.1, hm.2.trans (le_of_eq ?_)⟩
  ring

/-- The bounds on the fast path's triple `(fh, fl, eps)` from `2^800` to the threshold: those of
the Stirling case of `LgammaLeaf.LeafSpec` with `fh` up to the largest double. -/
def LeafTop (a : ℝ) (t : Float × Float × Float) : Prop :=
  Finite t.1.toBits ∧ Finite t.2.1.toBits ∧ Finite t.2.2.toBits ∧ 8 ≤ value t.1.toBits ∧
    value t.1.toBits ≤ 2 ^ 1024 - 2 ^ 971 ∧ |value t.2.1.toBits| ≤ value t.1.toBits / 2 ^ 17 ∧
    value t.1.toBits * (448 / 10 ^ 22) ≤ value t.2.2.toBits ∧
    value t.2.2.toBits ≤ value t.1.toBits / 2 ^ 62 ∧
    |GammaBasic.lgamma a - (value t.1.toBits + value t.2.1.toBits)| + value t.1.toBits / 2 ^ 67 ≤
      2 * value t.2.2.toBits

/-- The conclusion of `stir_top_core` gives `LeafTop`, as `LgammaLeaf.leaf_stir` does. -/
theorem leaf_stir_top (a : ℝ) (R : Float × Float) (hr1 : Finite R.1.toBits)
    (hr2 : Finite R.2.toBits) (hR1lo : 8 ≤ value R.1.toBits)
    (hR2r : |value R.2.toBits| ≤ value R.1.toBits / 2 ^ 17)
    (hR1hi : value R.1.toBits ≤ 2 ^ 1024 - 2 ^ 971)
    (hmain : |GammaBasic.lgamma a - (value R.1.toBits + value R.2.toBits)| +
        value R.1.toBits / 2 ^ 67 ≤
      2 * (value R.1.toBits * ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ)) -
        value R.1.toBits / 2 ^ 100) :
    LeafTop a (R.1, R.2, R.1.abs * Float.ofBits 0x3BEA90352E248A68) := by
  have hR1a : |value R.1.toBits| = value R.1.toBits := abs_of_pos (by linarith)
  obtain ⟨hef, hev⟩ := eps5_value_top R.1 hr1 (by rw [hR1a]; linarith [(by norm_num : (0 : ℝ) < 2 ^ 971)])
  rw [hR1a] at hev
  have hc5 := qcast_le LgammaStir.c5_bounds.1
  have hc5' := qcast_le LgammaStir.c5_bounds.2
  push_cast at hc5 hc5'
  set c := ((PolyBound.ratOfWord 0x3BEA90352E248A68 : ℚ) : ℝ) with hcdef
  set r := value R.1.toBits with hrdef
  have hp1 : r * (449 / 10 ^ 22) ≤ r * c := mul_le_mul_of_nonneg_left hc5 (by linarith)
  have hp2 : r * c ≤ r * (1 / 2 ^ 64) := mul_le_mul_of_nonneg_left hc5' (by linarith)
  have hp3 : r * c / 2 ^ 53 ≤ r * (1 / 2 ^ 64) / 2 ^ 53 :=
    div_le_div_of_nonneg_right hp2 (by norm_num)
  have hev' := abs_le.mp hev
  have hk : 1 / 2 ^ 1075 ≤ r / 2 ^ 1000 := by
    have : (8 : ℝ) / 2 ^ 1000 ≤ r / 2 ^ 1000 := div_le_div_of_nonneg_right hR1lo (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 8 / 2 ^ 1000)]
  refine ⟨hr1, hr2, hef, hR1lo, hR1hi, hR2r, ?_, ?_, ?_⟩
  · show r * (448 / 10 ^ 22) ≤ value (R.1.abs * Float.ofBits 0x3BEA90352E248A68).toBits
    linarith
  · show value (R.1.abs * Float.ofBits 0x3BEA90352E248A68).toBits ≤ r / 2 ^ 62
    linarith
  · show |GammaBasic.lgamma a - (r + value R.2.toBits)| + r / 2 ^ 67 ≤
      2 * value (R.1.abs * Float.ofBits 0x3BEA90352E248A68).toBits
    linarith

#print axioms abs_le_max
#print axioms stir_top_core
#print axioms leaf_stir_top

end Verified.Examples.LgammaStirTop
