import Library.Numerics.Float64.Tgamma.TgammaApprox
import Library.Numerics.Float64.Tgamma.TgammaPolyMainEdge
import Library.Numerics.Float64.Tgamma.TgammaPolySmall
import Library.Numerics.Float64.Tgamma.TgammaPolySmallAcc
import Library.Numerics.Float64.Tgamma.TgammaAccRangeA
import Library.Numerics.Float64.Tgamma.TgammaAccRangeB
import Library.Numerics.Float64.Tgamma.TgammaAccRangeC
import Library.Numerics.Float64.Tgamma.TgammaAsymFitB
import Library.Numerics.Float64.Tgamma.TgammaAsymFitC
import Library.Numerics.Float64.Tgamma.TgammaLogTables
import Library.Numerics.Float64.Tgamma.TgammaExpTables
import Library.Numerics.Float64.Tgamma.TgammaSinTables

/-!
Proofs of the approximation statements of `TgammaApprox`, which the floating-point proof of
`Tgamma.tgamma` takes as hypotheses.  Each statement follows from a theorem of the fact modules,
whose coefficient lists equal those of `TgammaApprox` by definition: `TgammaPolySmall`,
`TgammaPolyMain` with `TgammaPolyMainEdge`, and `TgammaPolySmallAcc` for the polynomials of `Γ`,
`TgammaAccRangeA` to `TgammaAccRangeC` for the nine ranges of the accurate path, `TgammaAsymFitB`
and `TgammaAsymFitC` for the two Stirling fits, and `TgammaLogTables`, `TgammaExpTables`, and
`TgammaSinTables` for the kernels and tables of the logarithm, the exponential, and the sine.  The
table of `sin (k π/128)`, the split `π`, and the cosine kernel meet tighter bounds than the
statements require (`2 ^ -80`, `2 ^ -80`, and `2 ^ -78 d²`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaFacts

open LeanExe.ProofKit PolyBound TgammaApprox

theorem smallFact : SmallFact := TgammaPolySmall.gamma_small_fast

theorem mainFact : MainFact := TgammaPolyMainEdge.gamma_main_wide

theorem accSmallFact : AccSmallFact := TgammaPolySmallAcc.gamma_small_acc

theorem accPoly_eq (oh imax ol jmax : ℕ) (d : ℝ) :
    accPoly oh imax ol jmax d = eval (TgammaAccRangeA.accList oh imax ol jmax) d := by
  rw [TgammaAccRangeA.accList, eval_addP]
  rfl

theorem accList_b (oh imax ol jmax : ℕ) :
    TgammaAccRangeB.accList oh imax ol jmax = TgammaAccRangeA.accList oh imax ol jmax := rfl

theorem accList_c (oh imax ol jmax : ℕ) :
    TgammaAccRangeC.accList oh imax ol jmax = TgammaAccRangeA.accList oh imax ol jmax := rfl

theorem accRangeFact : AccRangeFact := by
  unfold AccRangeFact
  intro oh imax ol jmax j eoff hm d hd
  rw [accPoly_eq]
  simp only [accRanges, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
  · exact TgammaAccRangeA.range160 d hd
  · exact TgammaAccRangeA.range128 d hd
  · exact TgammaAccRangeA.range96 d hd
  · rw [← accList_b]; exact TgammaAccRangeB.range64 d hd
  · rw [← accList_b]; exact TgammaAccRangeB.range32 d hd
  · rw [← accList_b]; exact TgammaAccRangeB.range26 d hd
  · rw [← accList_c]; exact TgammaAccRangeC.range16 d hd
  · rw [← accList_c]; exact TgammaAccRangeC.range8 d hd
  · rw [← accList_c]; exact TgammaAccRangeC.range4 d hd

theorem fit_eq_hi (x : ℝ) :
    GammaFits.fit TgammaFactsBase.c0Hi TgammaFactsBase.stirHiList x = stirHi x := by
  rw [GammaFits.fit, stirHi, one_div x, one_div (x ^ 2), inv_pow]
  rfl

theorem fit_eq_lo (x : ℝ) :
    GammaFits.fit TgammaFactsBase.c0Lo TgammaFactsBase.stirLoList x = stirLo x := by
  rw [GammaFits.fit, stirLo, one_div x, one_div (x ^ 2), inv_pow]
  rfl

theorem stirlingFact : StirlingFact := by
  unfold StirlingFact
  constructor
  · intro x h1 _
    have h := TgammaAsymFitC.asym_big h1
    rw [fit_eq_hi] at h
    exact h
  · intro x h1 h2
    have h := TgammaAsymFitB.asym_small h1 h2
    rw [fit_eq_lo] at h
    exact h

theorem logFact : LogFact := by
  unfold LogFact
  exact ⟨TgammaLogTables.log_poly, TgammaLogTables.l1_close, TgammaLogTables.l2_close,
    TgammaLogTables.ln2_close⟩

/-- The last conjunct of `ExpFact` on `|X| ≤ 5/8`, the interval of `TgammaApprox` at commit
`ef012e60` on branch `w/poly`. -/
theorem exp_poly_wide : ∀ X : ℝ, |X| ≤ 5 / 8 →
    |Real.exp (X * Real.log 2 / 1024) - (1 + X * expPoly X)| ≤ 1 / 2 ^ 74 :=
  TgammaExpTables.exp_poly

theorem expFact : ExpFact := by
  unfold ExpFact
  exact ⟨TgammaExpTables.invLn2_close, TgammaExpTables.e0_close, TgammaExpTables.e1_close,
    exp_poly_wide⟩

theorem sinFact : SinFact := by
  unfold SinFact
  refine ⟨fun k hk => (TgammaSinTables.st_close k hk).trans (by norm_num), TgammaSinTables.sin_poly,
    fun d hd => (TgammaSinTables.cos_poly d hd).trans ?_,
    TgammaSinTables.piDD_close.trans (by norm_num)⟩
  exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg d)

theorem allFacts : AllFacts := by
  unfold AllFacts
  exact ⟨smallFact, mainFact, accSmallFact, accRangeFact, stirlingFact, logFact, expFact,
    sinFact⟩

#print axioms allFacts

end Library.Numerics.Float64.Tgamma.TgammaFacts
