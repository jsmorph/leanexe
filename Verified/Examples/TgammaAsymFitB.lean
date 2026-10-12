import Verified.Examples.TgammaAsymFit

/-!
The bound on CORE-MATH's Stirling fit for `x ≤ 11.5` on `[8, 12]`, with eight pieces of radius
`1/4` and degree 18, and its combination with `TgammaAsymFit.fit_small_lo` into `asym_small` on
`[4, 12]`.
-/

namespace Verified.Examples.TgammaAsymFitB

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaThresholds
  TgammaFactsBase TgammaAsymFit

/-- The Taylor-model parameters: radius `1 / 4`, degree 18, 100 bits, at most 60 series terms with
remainder factor below `2 ^ -80`, and Mathlib's 20-digit bounds on `π`. -/
def cfgB : Cfg := ⟨1 / 4, 18, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfgB_pi : ((cfgB.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfgB.piHi : ℚ) : ℝ) := pi_bounds20

theorem smallB_piece0 : lgammaDiffOk cfgB ⟨(33 / 4), 8, log2Lo, log2Hi,
    ⟨4,
      (157231130946934297738233728311 / 10141204801825835211973625643008),
      (314462261893868595476467456625 / 20282409603651670423947251286016)⟩,
    ⟨28,
      (2945440518747216168601422753041 / 20282409603651670423947251286016),
      (736360129686804042150355688261 / 5070602400912917605986812821504)⟩⟩
    (fitExpr (33 / 4) ⟨3,
        (312061692631428082850567715063 / 10141204801825835211973625643008),
        (624123385262856165701135430129 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallB_piece1 : lgammaDiffOk cfgB ⟨(35 / 4), 8, log2Lo, log2Hi,
    ⟨4,
      (232281943384987193648107240905 / 5070602400912917605986812821504),
      (929127773539948774592428963623 / 20282409603651670423947251286016)⟩,
    ⟨29,
      (-1021902394132947198020713429311 / 5070602400912917605986812821504),
      (-4087609576531788792082853717241 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (35 / 4) ⟨3,
        (227193813501458473645071875491 / 2535301200456458802993406410752),
        (1817550508011667789160575003931 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallB_piece2 : lgammaDiffOk cfgB ⟨(37 / 4), 7, log2Lo, log2Hi,
    ⟨4,
      (157231130946934297738233728311 / 10141204801825835211973625643008),
      (314462261893868595476467456625 / 20282409603651670423947251286016)⟩,
    ⟨25,
      (1160658566742180001450143661457 / 10141204801825835211973625643008),
      (2321317133484360002900287322917 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (37 / 4) ⟨3,
        (736160247686873877612326322427 / 5070602400912917605986812821504),
        (2944640990747495510449305289711 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallB_piece3 : lgammaDiffOk cfgB ⟨(39 / 4), 7, log2Lo, log2Hi,
    ⟨4,
      (232281943384987193648107240905 / 5070602400912917605986812821504),
      (929127773539948774592428963623 / 20282409603651670423947251286016)⟩,
    ⟨25,
      (4076767473594828298324393943799 / 10141204801825835211973625643008),
      (8153534947189656596648787887601 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (39 / 4) ⟨3,
        (250773922272768585294370744087 / 1267650600228229401496703205376),
        (4012382756364297364709931905395 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallB_piece4 : lgammaDiffOk cfgB ⟨(41 / 4), 6, log2Lo, log2Hi,
    ⟨4,
      (157231130946934297738233728311 / 10141204801825835211973625643008),
      (314462261893868595476467456625 / 20282409603651670423947251286016)⟩,
    ⟨22,
      (-155830964315783876887254491699 / 5070602400912917605986812821504),
      (-623323857263135507549017966793 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (41 / 4) ⟨3,
        (628339323863808544527733165541 / 2535301200456458802993406410752),
        (5026714590910468356221865324331 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallB_piece5 : lgammaDiffOk cfgB ⟨(43 / 4), 6, log2Lo, log2Hi,
    ⟨4,
      (232281943384987193648107240905 / 5070602400912917605986812821504),
      (929127773539948774592428963623 / 20282409603651670423947251286016)⟩,
    ⟨22,
      (4141152190825359231938855982205 / 20282409603651670423947251286016),
      (32352751490823118999522312361 / 158456325028528675187087900672)⟩⟩
    (fitExpr (43 / 4) ⟨3,
        (5992726189133318487608924967967 / 20282409603651670423947251286016),
        (2996363094566659243804462483985 / 10141204801825835211973625643008)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallB_piece6 : lgammaDiffOk cfgB ⟨(45 / 4), 5, log2Lo, log2Hi,
    ⟨4,
      (157231130946934297738233728311 / 10141204801825835211973625643008),
      (314462261893868595476467456625 / 20282409603651670423947251286016)⟩,
    ⟨19,
      (-5650038448173603863770883291125 / 20282409603651670423947251286016),
      (-2825019224086801931885441645561 / 10141204801825835211973625643008)⟩⟩
    (fitExpr (45 / 4) ⟨3,
        (6914812681712546180764555659261 / 20282409603651670423947251286016),
        (3376373379742454189826443193 / 9903520314283042199192993792)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallB_piece7 : lgammaDiffOk cfgB ⟨(47 / 4), 5, log2Lo, log2Hi,
    ⟨4,
      (232281943384987193648107240905 / 5070602400912917605986812821504),
      (929127773539948774592428963623 / 20282409603651670423947251286016)⟩,
    ⟨19,
      (-1851573998307959255670068985763 / 20282409603651670423947251286016),
      (-57861687447123726739689655805 / 633825300114114700748351602688)⟩⟩
    (fitExpr (47 / 4) ⟨3,
        (7796795533734972933434662732015 / 20282409603651670423947251286016),
        (3898397766867486466717331366009 / 10141204801825835211973625643008)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallB_cover : ∀ x : ℝ, (8 : ℝ) ≤ x → x ≤ (8 : ℝ) + 2 * ((1 : ℝ) / 4) * 8 →
    |lgamma x - fit c0Lo stirLoList x| ≤ 1 / 2 ^ 64 := by
  refine cover_pieces (K := 8) (by norm_num) (lo := (8 : ℝ)) (r := ((1 : ℝ) / 4))
    (by norm_num) (fun x => |lgamma x - fit c0Lo stirLoList x| ≤ 1 / 2 ^ 64) ?_
  intro j hj t ht
  interval_cases j
  · have hb := fit_piece cfgB cfgB_pi _ _ c0Lo stirLoList _ _ smallB_piece0 t
      (by simp only [cfgB]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgB cfgB_pi _ _ c0Lo stirLoList _ _ smallB_piece1 t
      (by simp only [cfgB]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgB cfgB_pi _ _ c0Lo stirLoList _ _ smallB_piece2 t
      (by simp only [cfgB]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgB cfgB_pi _ _ c0Lo stirLoList _ _ smallB_piece3 t
      (by simp only [cfgB]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgB cfgB_pi _ _ c0Lo stirLoList _ _ smallB_piece4 t
      (by simp only [cfgB]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgB cfgB_pi _ _ c0Lo stirLoList _ _ smallB_piece5 t
      (by simp only [cfgB]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgB cfgB_pi _ _ c0Lo stirLoList _ _ smallB_piece6 t
      (by simp only [cfgB]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgB cfgB_pi _ _ c0Lo stirLoList _ _ smallB_piece7 t
      (by simp only [cfgB]; push_cast; exact ht)
    convert hb using 4 <;> norm_num

/-- The fit for `x ≤ 11.5` is within `2 ^ -64` of `lgamma` on `[4, 12]`. -/
theorem asym_small {x : ℝ} (h1 : 4 ≤ x) (h2 : x ≤ 12) :
    |lgamma x - fit c0Lo stirLoList x| ≤ 1 / 2 ^ 64 := by
  rcases le_or_gt x 8 with h | h
  · exact fit_small_lo h1 h
  · exact smallB_cover x h.le (by norm_num; linarith)

#print axioms asym_small

end Verified.Examples.TgammaAsymFitB
