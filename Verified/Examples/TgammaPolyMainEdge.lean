import Verified.Examples.TgammaPolyMain

/-!
The bound of `TgammaPolyMain.gamma_main` on the interval `|d| ≤ 1/2 + 2 ^ -50`.  The code's
`d = x - (i + 3.5)` with `i = roundeven (fl (x - 3.5))` exceeds `1/2` in magnitude by up to
`2 ^ -51` when `x - 3.5` rounds, so two pieces of radius `2 ^ -51` at the ends extend the eight
pieces of `TgammaPolyMain`.
-/

namespace Verified.Examples.TgammaPolyMainEdge

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaThresholds
  TgammaFactsBase TgammaPolyMain

/-- The Taylor-model parameters: radius `2 ^ -51`, degree 8, 100 bits, at most 60 series terms with
remainder factor below `2 ^ -80`, and Mathlib's 20-digit bounds on `π`. -/
def cfgE : Cfg := ⟨1 / 2 ^ 51, 8, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfgE_pi : ((cfgE.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfgE.piHi : ℚ) : ℝ) := pi_bounds20

theorem edge_lo : gammaPieceOk cfgE ⟨(6755399441055743 / 2251799813685248), 14, log2Lo, log2Hi,
    ⟨4,
      (614806705873704048773093354185 / 10141204801825835211973625643008),
      (1229613411747408097546186708373 / 20282409603651670423947251286016)⟩,
    ⟨43,
      (1758324290587092039435855707167 / 10141204801825835211973625643008),
      (3516648581174184078871711414337 / 20282409603651670423947251286016)⟩⟩
    (PolyBound.shift (-1125899906842625 / 2 ^ 51) mainList) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

theorem edge_hi : gammaPieceOk cfgE ⟨(9007199254740993 / 2251799813685248), 13, log2Lo, log2Hi,
    ⟨4,
      (614806705873704578608343633067 / 10141204801825835211973625643008),
      (1229613411747409157216687266137 / 20282409603651670423947251286016)⟩,
    ⟨42,
      (-4707160821464481085956546707669 / 20282409603651670423947251286016),
      (-2353580410732240542978273353833 / 10141204801825835211973625643008)⟩⟩
    (PolyBound.shift (1125899906842625 / 2 ^ 51) mainList) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

/-- CORE-MATH's polynomial about 3.5 is within `2 ^ -62` of `Γ (7/2 + d)` for
`|d| ≤ 1/2 + 2 ^ -50`. -/
theorem gamma_main_wide : ∀ d : ℝ, |d| ≤ 1 / 2 + 1 / 2 ^ 50 →
    |Real.Gamma (7 / 2 + d) - eval mainList d| ≤ 1 / 2 ^ 62 := by
  intro d hd
  have hd' := abs_le.mp hd
  rcases le_or_gt d (1 / 2) with h1 | h1
  · rcases le_or_gt (-1 / 2) d with h2 | h2
    · exact gamma_main d (abs_le.mpr ⟨by linarith, h1⟩)
    · have ht : |d - ((-1125899906842625 : ℝ) / 2 ^ 51)| ≤ ((cfgE.r : ℚ) : ℝ) := by
        simp only [cfgE]
        rw [abs_le]
        constructor <;> push_cast <;> linarith
      have hb := piece_bound cfgE cfgE_pi _ mainList _ _ (7 / 2) (-1125899906842625 / 2 ^ 51)
        (by norm_num) edge_lo (d - ((-1125899906842625 : ℝ) / 2 ^ 51)) ht
      have e : (((-1125899906842625 / 2 ^ 51) : ℚ) : ℝ) +
          (d - ((-1125899906842625 : ℝ) / 2 ^ 51)) = d := by
        push_cast
        ring
      rw [e] at hb
      push_cast at hb
      exact hb
  · have ht : |d - ((1125899906842625 : ℝ) / 2 ^ 51)| ≤ ((cfgE.r : ℚ) : ℝ) := by
      simp only [cfgE]
      rw [abs_le]
      constructor <;> push_cast <;> linarith
    have hb := piece_bound cfgE cfgE_pi _ mainList _ _ (7 / 2) (1125899906842625 / 2 ^ 51)
      (by norm_num) edge_hi (d - ((1125899906842625 : ℝ) / 2 ^ 51)) ht
    have e : (((1125899906842625 / 2 ^ 51) : ℚ) : ℝ) +
        (d - ((1125899906842625 : ℝ) / 2 ^ 51)) = d := by
      push_cast
      ring
    rw [e] at hb
    push_cast at hb
    exact hb

#print axioms gamma_main_wide

end Verified.Examples.TgammaPolyMainEdge
