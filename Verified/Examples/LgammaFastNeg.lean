import Verified.Examples.LgammaReflWin

/-!
`FastSpec` for the fast path of `Lgamma.lgammaWith` at a negative non-integer `x` from `-1/2`
down, where the code evaluates a positive leaf at `a = |x|` and the reflection.  `neg_piece` takes
the leaf of a piece, from 0.5 to 8.29541, and applies `LgammaReflMid.refl_two` from -2 to -1/2,
`LgammaReflWin.refl_four` from -4 to -2, `LgammaReflMid.refl_six` from -6 to -4, and
`LgammaReflTail.refl_tail` below -6, where `ln Γ a ≥ ln 64` gives `|fh| ≥ 4`.  `neg_stir` takes
the leaf of Stirling's series, from 8.29541 to `2^52`, and applies `refl_tail`.  Below `-2^52`
every double is an integer.
-/

namespace Verified.Examples.LgammaFastNeg
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaWords LgammaFastSmall
  LgammaPiecePoly TgammaFloor LgammaWalk LgammaReflCore LgammaReflTail LgammaReflMid
  LgammaReflWin

set_option exponentiation.threshold 4096

theorem border_le : ∀ k, k < 20 → LgammaApprox.border k ≤ 9 := by decide +kernel

set_option maxHeartbeats 1000000 in
/-- **The reflection of a piece**: `FastSpec` at a negative non-integer `x` from `-1/2` down to
`-8.29541`, from the piece at `|x|`. -/
theorem neg_piece (hF : FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (hPF : LgammaApprox.PieceFact) (x : Float)
    (hx : Finite x.toBits) (hneg : value x.toBits ≤ -1 / 2)
    (hint : ∀ n : ℤ, value x.toBits ≠ n) (k : ℕ) (hk : k < 19) (jj : UInt64)
    (hjj : jj.toNat = k) (hb0 : (LgammaApprox.border k : ℝ) ≤ value x.abs.toBits)
    (hb1 : value x.abs.toBits ≤ (LgammaApprox.border (k + 1) : ℝ)) (P Q R : Float × Float)
    (hP : P = Lgamma.piecePoly Lgamma.mainTable jj (x.abs - entry Lgamma.mainTable (20 + jj)))
    (hQ : Q = if jj == 4 then mulDDD (1.0 - x.abs) P.1 P.2 else (P.1, P.2))
    (hR : R = if jj == 10 then mulDDD (x.abs - 2.0) Q.1 Q.2 else (Q.1, Q.2))
    (A B C D : Float × Float)
    (hA : A = Lgamma.asSinpipid Lgamma.sinpiTable (x - floorF x))
    (hB : B = mulDDD (-x) A.1 A.2)
    (hC : C = Lgamma.asLogd Tgamma.logdTable B.1)
    (hD : D = sumDD R.1 R.2 C.1 (C.2 + B.2 / B.1)) (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (-D.1, -D.2, (R.1.abs * Float.ofBits 0x3BF9AD88BDABDB20 + Float.ofBits 0x3AF357C299A88EA7) +
        C.1.abs * Float.ofBits 0x3B8E392010175EE6, sign) := by
  obtain ⟨haf, hav⟩ := SinhWords.abs_float x hx
  set v := value x.toBits with hvdef
  have hav' : value x.abs.toBits = -v := by rw [hav, abs_of_neg (by linarith)]
  have hm1 : v ≠ -1 := by have := hint (-1); push_cast at this; exact this
  have hm2 : v ≠ -2 := by have := hint (-2); push_cast at this; exact this
  have hm4 : v ≠ -4 := by have := hint (-4); push_cast at this; exact this
  have hm6 : v ≠ -6 := by have := hint (-6); push_cast at this; exact this
  obtain ⟨hr1, hr2, hef, hr1b, hr2b, helo, hehi, hpos⟩ := piece_iface hF hPF x.abs haf k hk jj hjj
    hb0 hb1 (by rw [hav']; intro h; exact hm1 (by linarith))
    (by rw [hav']; intro h; exact hm2 (by linarith)) P Q R hP hQ hR
  rw [hav'] at hpos
  have h9 : -9 ≤ v := by
    have := qcast_le (border_le (k + 1) (by omega))
    push_cast at this
    linarith
  rcases lt_or_gt_of_ne hm2 with h2 | h2
  · rcases lt_or_gt_of_ne hm4 with h4 | h4
    · rcases lt_or_gt_of_ne hm6 with h6 | h6
      · -- below -6
        have hlg : (4158 / 1000 : ℝ) ≤ GammaBasic.lgamma (-v) :=
          log_bounds.2.2.trans (lgamma_six.trans
            (GammaThresholds.lgamma_mono (by norm_num) (by linarith)))
        have hF4 : 4 ≤ |value R.1.toBits| := by
          have h1 : GammaBasic.lgamma (-v) - (value R.1.toBits + value R.2.toBits) ≤
              2 * value (R.1.abs * Float.ofBits 0x3BF9AD88BDABDB20 +
                Float.ofBits 0x3AF357C299A88EA7).toBits := by
            have := le_abs_self (GammaBasic.lgamma (-v) - (value R.1.toBits + value R.2.toBits))
            have : 0 ≤ |value R.1.toBits| / 2 ^ 65 := by positivity
            linarith
          have h3 : |value R.1.toBits| / 2 ^ 63 ≤ 16 / 2 ^ 63 :=
            div_le_div_of_nonneg_right hr1b (by norm_num)
          have h4 := le_abs_self (value R.1.toBits)
          have h5 := le_abs_self (value R.2.toBits)
          linarith [(by norm_num : (4158 : ℝ) / 1000 - 1 / 2 ^ 38 -
            2 * (16 / 2 ^ 63 + 1 / 2 ^ 78) ≥ 4)]
        refine refl_tail hF hL hS x hx (by linarith) (by linarith) hint R.1 R.2 _ hr1 hr2 hef hF4
          (by linarith [(by norm_num : (16 : ℝ) ≤ 2 ^ 60)])
          (by have : 0 ≤ |value R.1.toBits| / 2 ^ 17 := by positivity
              linarith)
          (by have := mul_le_mul_of_nonneg_left (by norm_num : (448 : ℝ) / 10 ^ 22 ≤ 869 / 10 ^ 22)
                (abs_nonneg (value R.1.toBits))
              linarith)
          (by have : |value R.1.toBits| / 2 ^ 63 ≤ |value R.1.toBits| / 2 ^ 62 :=
                div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
              linarith)
          (by have : |value R.1.toBits| / 2 ^ 67 ≤ |value R.1.toBits| / 2 ^ 65 :=
                div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
              linarith)
          A B C D hA hB hC hD sign
      · exact refl_six hF hL hS x hx h6 h4 hint R.1 R.2 _ hr1 hr2 hef hr1b hr2b helo hehi hpos
          A B C D hA hB hC hD sign
    · exact refl_four hF hL hS x hx h4 h2 hint R.1 R.2 _ hr1 hr2 hef hr1b hr2b helo hehi hpos
        A B C D hA hB hC hD sign
  · exact refl_two hF hL hS x hx h2 hneg hint R.1 R.2 _ hr1 hr2 hef hr1b hr2b helo hehi hpos
      A B C D hA hB hC hD sign

set_option maxHeartbeats 1000000 in
/-- **The reflection of Stirling's series**: `FastSpec` at a negative non-integer `x` from
`-8.29541` down to `-2^52`, from the leaf of `LgammaStir.stir_a` at `|x|`. -/
theorem neg_stir (hF : FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (hSF : LgammaApprox.StirlingFact) (x : Float)
    (hx : Finite x.toBits) (hneg : value x.toBits < 0) (hint : ∀ n : ℤ, value x.toBits ≠ n)
    (hb : (LgammaApprox.border 19 : ℝ) ≤ value x.abs.toBits)
    (h52 : value x.abs.toBits < 2 ^ 52) (L0 M N E T R : Float × Float)
    (hL0 : L0 = Lgamma.asLogd Tgamma.logdTable x.abs)
    (hM : M = mulDDD (x.abs - 0.5) (L0.1 - 1.0) L0.2)
    (hN : N = fastSum M.1 M.2 (entry Lgamma.mainTable 397) (entry Lgamma.mainTable 398))
    (hE : E = fastTwoSum (entry Lgamma.mainTable 399)
      (TgammaExpr.evalF LgammaStirSeries.sE ((1.0 / x.abs) * (1.0 / x.abs))))
    (hT : T = mulDD E.1 (E.2 + entry Lgamma.mainTable 400) (1.0 / x.abs)
      (Fma.fma (1.0 / x.abs) (-x.abs) 1.0 * (1.0 / x.abs)))
    (hR : R = fastSum N.1 N.2 T.1 T.2)
    (A B C D : Float × Float)
    (hA : A = Lgamma.asSinpipid Lgamma.sinpiTable (x - floorF x))
    (hB : B = mulDDD (-x) A.1 A.2)
    (hC : C = Lgamma.asLogd Tgamma.logdTable B.1)
    (hD : D = sumDD R.1 R.2 C.1 (C.2 + B.2 / B.1)) (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (-D.1, -D.2, R.1.abs * Float.ofBits 0x3BEA90352E248A68 +
        C.1.abs * Float.ofBits 0x3B8E392010175EE6, sign) := by
  obtain ⟨haf, hav⟩ := SinhWords.abs_float x hx
  have hav' : value x.abs.toBits = -value x.toBits := by rw [hav, abs_of_neg hneg]
  obtain ⟨hr1, hr2, hR1lo, hR2r, hR1hi, hmain⟩ :=
    LgammaStir.stir_a hF hL hSF x.abs haf hb h52 L0 M N E T R hL0 hM hN hE hT hR
  rw [hav'] at hmain hb h52
  have hb19 := qcast_le LgammaStir.border19
  push_cast at hb19
  have hR1a : |value R.1.toBits| = value R.1.toBits := abs_of_pos (by linarith)
  obtain ⟨hef, hev⟩ := LgammaFastPos.eps5_value R.1 hr1
    (by rw [hR1a]; linarith [(by norm_num : (2 : ℝ) ^ 58 ≤ 2 ^ 900)])
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
  refine refl_tail hF hL hS x hx (by linarith) (by linarith) hint R.1 R.2 _ hr1 hr2 hef
    (by rw [hR1a]; linarith) (by rw [hR1a]; linarith [(by norm_num : (2 : ℝ) ^ 58 ≤ 2 ^ 60)])
    (by rw [hR1a]; have : 0 ≤ 1 / (2 : ℝ) ^ 38 := by norm_num
        linarith) ?_ ?_ ?_ A B C D hA hB hC hD sign
  · rw [hR1a]; linarith
  · rw [hR1a]; linarith
  · rw [hR1a]
    have : 0 ≤ r / 2 ^ 67 := by positivity
    linarith

#print axioms neg_piece
#print axioms neg_stir

end Verified.Examples.LgammaFastNeg
