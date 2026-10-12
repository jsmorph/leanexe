import Verified.Examples.TgammaAsymFit

/-!
The bound on CORE-MATH's Stirling fit for `x > 11.5` from 11 on: five pieces of radius `1/2` and
degree 22 on `[11, 16]`, and from 16 on `GammaFits.fit_large`, which compares the fit with
Stirling's series.
`asym_big` bounds `|lgamma x - fit|` by `2 ^ -64` from 11 on.  An absolute error in `lgamma` is a
relative error in `Γ = exp lgamma`.
-/

namespace Verified.Examples.TgammaAsymFitC

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaThresholds
  TgammaFactsBase TgammaAsymFit

/-- The Taylor-model parameters: radius `1 / 2`, degree 22, 100 bits, at most 60 series terms with
remainder factor below `2 ^ -80`, and Mathlib's 20-digit bounds on `π`. -/
def cfgC : Cfg := ⟨1 / 2, 22, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfgC_pi : ((cfgC.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfgC.piHi : ℚ) : ℝ) := pi_bounds20

theorem big_piece0 : lgammaDiffOk cfgC ⟨(23 / 2), 5, log2Lo, log2Hi,
    ⟨4,
      (312061692631428082850567715063 / 10141204801825835211973625643008),
      (624123385262856165701135430129 / 20282409603651670423947251286016)⟩,
    ⟨19,
      (-933205795583571297814404672573 / 5070602400912917605986812821504),
      (-3732823182334285191257618690289 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (23 / 2) ⟨3,
        (3680298935211598694926600631719 / 10141204801825835211973625643008),
        (7360597870423197389853201263441 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Hi stirHiList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem big_piece1 : lgammaDiffOk cfgC ⟨(25 / 2), 4, log2Lo, log2Hi,
    ⟨4,
      (312061692631428082850567715063 / 10141204801825835211973625643008),
      (624123385262856165701135430129 / 20282409603651670423947251286016)⟩,
    ⟨15,
      (46332405921494228074709322735 / 316912650057057350374175801344),
      (2965273978975630596781396655043 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (25 / 2) ⟨4,
        (-5006917215396578631098987695111 / 20282409603651670423947251286016),
        (-1251729303849144657774746923777 / 5070602400912917605986812821504)⟩
      log2Lo log2Hi c0Hi stirHiList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem big_piece2 : lgammaDiffOk cfgC ⟨(27 / 2), 3, log2Lo, log2Hi,
    ⟨4,
      (312061692631428082850567715063 / 10141204801825835211973625643008),
      (624123385262856165701135430129 / 20282409603651670423947251286016)⟩,
    ⟨11,
      (7972191194372209227880384350149 / 20282409603651670423947251286016),
      (996523899296526153485048043769 / 2535301200456458802993406410752)⟩⟩
    (fitExpr (27 / 2) ⟨4,
        (-1722980927775069113947098250371 / 10141204801825835211973625643008),
        (-3445961855550138227894196500739 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Hi stirHiList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem big_piece3 : lgammaDiffOk cfgC ⟨(29 / 2), 2, log2Lo, log2Hi,
    ⟨4,
      (312061692631428082850567715063 / 10141204801825835211973625643008),
      (624123385262856165701135430129 / 20282409603651670423947251286016)⟩,
    ⟨8,
      (-2640541981810765722117635757883 / 20282409603651670423947251286016),
      (-330067747726345715264704469735 / 2535301200456458802993406410752)⟩⟩
    (fitExpr (29 / 2) ⟨4,
        (-1996601878211682619325906414799 / 20282409603651670423947251286016),
        (-499150469552920654831476603699 / 5070602400912917605986812821504)⟩
      log2Lo log2Hi c0Hi stirHiList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem big_piece4 : lgammaDiffOk cfgC ⟨(31 / 2), 1, log2Lo, log2Hi,
    ⟨4,
      (312061692631428082850567715063 / 10141204801825835211973625643008),
      (624123385262856165701135430129 / 20282409603651670423947251286016)⟩,
    ⟨4,
      (-321970051799541551395864671543 / 10141204801825835211973625643008),
      (-643940103599083102791729343083 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (31 / 2) ⟨4,
        (-321970051799541551395864671543 / 10141204801825835211973625643008),
        (-643940103599083102791729343083 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Hi stirHiList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem big_cover : ∀ x : ℝ, (11 : ℝ) ≤ x → x ≤ (11 : ℝ) + 2 * ((1 : ℝ) / 2) * 5 →
    |lgamma x - fit c0Hi stirHiList x| ≤ 1 / 2 ^ 64 := by
  refine cover_pieces (K := 5) (by norm_num) (lo := (11 : ℝ)) (r := ((1 : ℝ) / 2))
    (by norm_num) (fun x => |lgamma x - fit c0Hi stirHiList x| ≤ 1 / 2 ^ 64) ?_
  intro j hj t ht
  interval_cases j
  · have hb := fit_piece cfgC cfgC_pi _ _ c0Hi stirHiList _ _ big_piece0 t
      (by simp only [cfgC]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgC cfgC_pi _ _ c0Hi stirHiList _ _ big_piece1 t
      (by simp only [cfgC]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgC cfgC_pi _ _ c0Hi stirHiList _ _ big_piece2 t
      (by simp only [cfgC]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgC cfgC_pi _ _ c0Hi stirHiList _ _ big_piece3 t
      (by simp only [cfgC]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgC cfgC_pi _ _ c0Hi stirHiList _ _ big_piece4 t
      (by simp only [cfgC]; push_cast; exact ht)
    convert hb using 4 <;> norm_num

theorem big_large : fitLargeOk c0Hi stirHiList (5 / 2 ^ 63) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

/-- The fit for `x > 11.5` is within `2 ^ -64` of `lgamma` from 11 on. -/
theorem asym_big {x : ℝ} (h1 : 11 ≤ x) : |lgamma x - fit c0Hi stirHiList x| ≤ 1 / 2 ^ 64 := by
  rcases le_or_gt x 16 with h | h
  · exact big_cover x h1 (by norm_num; linarith)
  · have hl := fit_large _ _ _ _ _ big_large h.le
    push_cast at hl
    exact hl

#print axioms asym_big

end Verified.Examples.TgammaAsymFitC
