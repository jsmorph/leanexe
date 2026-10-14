import Verified.Examples.TgammaCases
import Verified.Examples.FmaSpecTheorem

/-!
**`Tgamma.tgamma` within one step of `Γ`** for every finite input other than the poles
(`tgamma_within_one`), and the canonical NaN at the negative integers (`tgamma_neg_int`).
`TgammaSpecial` gives the exact results at `±0`, `±∞`, and NaN.  The fused multiply-add enters
through `FmaSpecTheorem.fma_nearest`.  The theorem takes as hypotheses the approximation facts of
`TgammaApprox` that track `erf` proves, the specifications of `asLogd` and `asSinpid` that track
`expm1` proves, `GammaBelowT0` and `SubnormalGap` from track `erf`, and `AccurateWithin`, the
accurate path within one step at the inputs where the fast paths call it.
-/

namespace Verified.Examples.TgammaFinal
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaFloor TgammaBranches TgammaCases

set_option exponentiation.threshold 4096

/-- The accurate path within one step at the inputs where the fast paths call it. -/
def AccurateWithin : Prop :=
  ∀ x : Float, Finite x.toBits → (∀ n : ℤ, value x.toBits ≠ n) → 1 / 2 ^ 112 ≤ |value x.toBits| →
    -184 < value x.toBits → value x.toBits < (GammaThresholds.t0 : ℝ) →
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (accurate accurateTable dbTable x).toBits

/-- **`tgamma` within one step of `Γ`** for every finite `x` other than `0` and the negative
integers. -/
theorem tgamma_within_one (hS : TgammaApprox.SmallFact) (hM : TgammaApprox.MainFact)
    (hSt : TgammaApprox.StirlingFact) (hE : TgammaApprox.ExpFact) (hLog : TgammaAsym1.LogdSpec)
    (hSin : TgammaRefl4.SinpidSpec) (hT : TgammaLarge.GammaBelowT0)
    (hGap : TgammaRefl4.SubnormalGap) (hAcc : AccurateWithin) (x : Float) (hx : Finite x.toBits)
    (hpole : ∀ n : ℤ, n ≤ 0 → value x.toBits ≠ n) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits)) (tgamma x).toBits := by
  have hF := FmaSpecTheorem.fma_nearest
  have ht0 : (GammaThresholds.t0 : ℝ) < 172 := by
    have : GammaThresholds.t0 < 172 := by unfold GammaThresholds.t0; norm_num
    exact_mod_cast this
  have ht1 : (1 : ℝ) < GammaThresholds.t0 := by
    have : (1 : ℚ) < GammaThresholds.t0 := by unfold GammaThresholds.t0; norm_num
    exact_mod_cast this
  unfold tgamma
  have h1 := TgammaSpecial.not_special x hx
  by_cases hq : x.abs < 0.25
  · have hq' := (TgammaSpecial.quarter_test x hx).mp hq
    have hx0 : value x.toBits ≠ 0 := by
      have := hpole 0 le_rfl
      simpa using this
    by_cases ht : x.toBits <<< 1 < 0x71E0000000000000
    · rw [tgamma_tiny _ _ _ _ _ _ _ _ x h1 hq ht]
      exact TgammaTiny.tinyPath_within hF x hx hx0 ((tiny_test x).mp ht)
    · rw [tgamma_small _ _ _ _ _ _ _ _ x h1 hq ht]
      have h112 : 1 / 2 ^ 112 ≤ |value x.toBits| := not_lt.mp (fun h => ht ((tiny_test x).mpr h))
      apply TgammaSmallPath.smallPath_within hF hS dbTable accurateTable x hx h112 hq'.le
      have hxa := abs_lt.mp hq'
      apply hAcc x hx _ h112 (by linarith) (by linarith)
      intro n hn
      have : (n : ℝ) = 0 := by
        have h3 : |(n : ℝ)| < 1 := by rw [← hn]; linarith
        have h4 : |n| < 1 := by exact_mod_cast h3
        have : n = 0 := by rw [abs_lt] at h4; omega
        rw [this]; norm_num
      exact hx0 (by rw [hn, this])
  · have hq' : 1 / 4 ≤ |value x.toBits| :=
      not_lt.mp (fun h => hq ((TgammaSpecial.quarter_test x hx).mpr h))
    by_cases ho : x ≥ Float.ofBits 0x406573FAE561F648
    · rw [tgamma_overflow _ _ _ _ _ _ _ _ x h1 hq ho]
      exact TgammaEdge.overflowPath_within _ ((t0_test x hx).mp ho)
    · have hot : value x.toBits < (GammaThresholds.t0 : ℝ) :=
        not_le.mp (fun h => ho ((t0_test x hx).mpr h))
      by_cases hi : (floorF x == x) = true
      · rw [tgamma_int _ _ _ _ _ _ _ _ x h1 hq ho hi]
        have hiv := (int_test x hx).mp hi
        have hn1 : 1 ≤ ⌊value x.toBits⌋ := by
          by_contra hc
          rw [not_le] at hc
          exact hpole ⌊value x.toBits⌋ (by omega) hiv.symm
        have hn171 : ⌊value x.toBits⌋ ≤ 171 := by
          have : (⌊value x.toBits⌋ : ℝ) < 172 := by rw [hiv]; linarith
          have : ⌊value x.toBits⌋ < 172 := by exact_mod_cast this
          omega
        obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = ⌊value x.toBits⌋ :=
          ⟨_, Int.toNat_of_nonneg (by omega)⟩
        apply TgammaInt.intPath_within hF x hx m (by omega) (by omega)
        rw [← hiv, ← hm, Int.cast_natCast]
      · have hi' : (floorF x == x) = false := by simpa using hi
        have hint : ∀ n : ℤ, value x.toBits ≠ n := by
          intro n hn
          apply hi
          rw [int_test x hx, hn, Int.floor_intCast]
        by_cases h184 : x ≤ -184.0
        · rw [tgamma_underflow _ _ _ _ _ _ _ _ x h1 hq ho hi' h184]
          exact TgammaEdge.underflowPath_within x hx ((m184_test x hx).mp h184) hint
        · have h184' : -184 < value x.toBits :=
            not_le.mp (fun h => h184 ((m184_test x hx).mpr h))
          have hacc := hAcc x hx hint (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 112 ≤ 1 / 4)])
            h184' hot
          by_cases h3 : x < -3.0
          · rw [tgamma_refl _ _ _ _ _ _ _ _ x h1 hq ho hi' h184 h3]
            exact TgammaReflPath.reflPath_within hF hLog hSt hE hSin hGap dbTable accurateTable x hx
              h184' ((m3_test x hx).mp h3) hint hacc
          · have h3' : -3 ≤ value x.toBits := not_lt.mp (fun h => h3 ((m3_test x hx).mpr h))
            by_cases h4 : x > 4.0
            · rw [tgamma_large _ _ _ _ _ _ _ _ x h1 hq ho hi' h184 h3 h4]
              exact TgammaLarge.largePath_within hF hLog hSt hE hT dbTable accurateTable x hx
                ((p4_test x hx).mp h4) hot hacc
            · have h4' : value x.toBits ≤ 4 := not_lt.mp (fun h => h4 ((p4_test x hx).mpr h))
              rw [tgamma_main _ _ _ _ _ _ _ _ x h1 hq ho hi' h184 h3 h4]
              have hm3 : -3 < value x.toBits := by
                rcases h3'.lt_or_eq with h | h
                · exact h
                · exact absurd h.symm (by have := hint (-3); push_cast at this; exact this)
              have hp4 : value x.toBits < 4 := by
                rcases h4'.lt_or_eq with h | h
                · exact h
                · exact absurd h (by have := hint 4; push_cast at this; exact this)
              exact TgammaMainPath.mainPath_within hF hM dbTable accurateTable x hx hm3 hp4 hq' hint
                hacc

/-- **The canonical NaN** at the negative integers. -/
theorem tgamma_neg_int (x : Float) (hx : Finite x.toBits) (n : ℤ) (hn : n < 0)
    (hv : value x.toBits = n) : (tgamma x).toBits = Wasm.IEEE64.canonicalNaN := by
  unfold tgamma
  have h1 := TgammaSpecial.not_special x hx
  have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
  have hq : ¬ x.abs < 0.25 := by
    rw [TgammaSpecial.quarter_test x hx, hv, abs_of_neg (by linarith)]
    linarith
  have ho : ¬ x ≥ Float.ofBits 0x406573FAE561F648 := by
    rw [t0_test x hx, hv]
    have : (0 : ℝ) < GammaThresholds.t0 := by
      have : (0 : ℚ) < GammaThresholds.t0 := by unfold GammaThresholds.t0; norm_num
      exact_mod_cast this
    linarith
  have hi : (floorF x == x) = true := by
    rw [int_test x hx, hv, Int.floor_intCast]
  rw [tgamma_int _ _ _ _ _ _ _ _ x h1 hq ho hi]
  exact TgammaEdge.intPath_neg x hx (by rw [hv]; linarith)

#print axioms tgamma_within_one
#print axioms tgamma_neg_int

end Verified.Examples.TgammaFinal
