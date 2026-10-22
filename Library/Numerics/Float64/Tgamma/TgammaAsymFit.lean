import Library.Numerics.Float64.Tgamma.TgammaFactsBase

/-!
The Stirling fits of CORE-MATH's `as_lgamma_asym` (`tgamma.c` lines 1058-1105, commit `ff2f71f6`),
which `cr_tgamma` uses for `x > 4` and, at `1 - x`, for `-184 < x < -3`, and a bound on the fit for
`x ≤ 11.5` on `[4, 8]`.  The fit is `(x - 1/2) (log x - 1) + C0 + x⁻¹ P (x⁻²)`
(`GammaFits.fit`), with `C0` the double-double `c [0]` and `P` built by `polydd` and the doubles
`q`: for `x ≤ 11.5` the double-doubles `c [1]`, `c [2]` and the high parts of `c [3]` to `c [12]`
(`Tgamma.asymTable` from word 16, `c0Lo` and `stirLoList`), and for `x > 11.5` the double-double
`c [1]` and the high parts of `c [2]` to `c [7]` (from word 0, `c0Hi` and `stirHiList`).
`fit_small_lo` bounds `|lgamma x - fit|` by `2 ^ -64` on `[4, 8]` with 16 pieces of radius `1/8`
and degree 16, small enough that each kernel check stays near 30000 coefficient operations.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAsymFit

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaThresholds
  TgammaFactsBase

/-- The Taylor-model parameters: radius `1 / 8`, degree 16, 100 bits, at most 60 series terms with
remainder factor below `2 ^ -80`, and Mathlib's 20-digit bounds on `π`. -/
def cfgA : Cfg := ⟨1 / 8, 16, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfgA_pi : ((cfgA.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfgA.piHi : ℚ) : ℝ) := pi_bounds20

theorem smallA_piece0 : lgammaDiffOk cfgA ⟨(33 / 8), 12, log2Lo, log2Hi,
    ⟨4,
      (39460140009725338086696816199 / 5070602400912917605986812821504),
      (157840560038901352346787264799 / 20282409603651670423947251286016)⟩,
    ⟨38,
      (-976765127188573014210645690369 / 20282409603651670423947251286016),
      (-488382563594286507105322845183 / 10141204801825835211973625643008)⟩⟩
    (fitExpr (33 / 8) ⟨2,
        (312061692631428082850567715063 / 10141204801825835211973625643008),
        (624123385262856165701135430129 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece1 : lgammaDiffOk cfgA ⟨(35 / 8), 12, log2Lo, log2Hi,
    ⟨4,
      (469883785660160440906038844505 / 20282409603651670423947251286016),
      (117470946415040110226509711127 / 5070602400912917605986812821504)⟩,
    ⟨38,
      (3143427754104404237425010587537 / 10141204801825835211973625643008),
      (6286855508208808474850021175077 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (35 / 8) ⟨2,
        (227193813501458473645071875491 / 2535301200456458802993406410752),
        (1817550508011667789160575003931 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece2 : lgammaDiffOk cfgA ⟨(37 / 8), 12, log2Lo, log2Hi,
    ⟨4,
      (777198901322680523450135614811 / 20282409603651670423947251286016),
      (388599450661340261725067807407 / 10141204801825835211973625643008)⟩,
    ⟨39,
      (-753970477581826786674752089423 / 20282409603651670423947251286016),
      (-188492619395456696668688022355 / 5070602400912917605986812821504)⟩⟩
    (fitExpr (37 / 8) ⟨2,
        (736160247686873877612326322427 / 5070602400912917605986812821504),
        (2944640990747495510449305289711 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece3 : lgammaDiffOk cfgA ⟨(39 / 8), 12, log2Lo, log2Hi,
    ⟨4,
      (539963526309064522751208978045 / 10141204801825835211973625643008),
      (1079927052618129045502417956093 / 20282409603651670423947251286016)⟩,
    ⟨39,
      (6036473591196241679465953241885 / 20282409603651670423947251286016),
      (188639799724882552483311038809 / 633825300114114700748351602688)⟩⟩
    (fitExpr (39 / 8) ⟨2,
        (250773922272768585294370744087 / 1267650600228229401496703205376),
        (4012382756364297364709931905395 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece4 : lgammaDiffOk cfgA ⟨(41 / 8), 11, log2Lo, log2Hi,
    ⟨4,
      (39460140009725338086696816199 / 5070602400912917605986812821504),
      (157840560038901352346787264799 / 20282409603651670423947251286016)⟩,
    ⟨36,
      (-100055532028214323744486320031 / 1267650600228229401496703205376),
      (-1600888512451429179911781120493 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (41 / 8) ⟨2,
        (628339323863808544527733165541 / 2535301200456458802993406410752),
        (5026714590910468356221865324331 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece5 : lgammaDiffOk cfgA ⟨(43 / 8), 11, log2Lo, log2Hi,
    ⟨4,
      (469883785660160440906038844505 / 20282409603651670423947251286016),
      (117470946415040110226509711127 / 5070602400912917605986812821504)⟩,
    ⟨36,
      (558663125024642585711180771393 / 2535301200456458802993406410752),
      (4469305000197140685689446171147 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (43 / 8) ⟨2,
        (5992726189133318487608924967967 / 20282409603651670423947251286016),
        (2996363094566659243804462483985 / 10141204801825835211973625643008)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece6 : lgammaDiffOk cfgA ⟨(45 / 8), 11, log2Lo, log2Hi,
    ⟨4,
      (777198901322680523450135614811 / 20282409603651670423947251286016),
      (388599450661340261725067807407 / 10141204801825835211973625643008)⟩,
    ⟨37,
      (-3698611468329322297124057379133 / 20282409603651670423947251286016),
      (-1849305734164661148562028689565 / 10141204801825835211973625643008)⟩⟩
    (fitExpr (45 / 8) ⟨2,
        (6914812681712546180764555659261 / 20282409603651670423947251286016),
        (3376373379742454189826443193 / 9903520314283042199192993792)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece7 : lgammaDiffOk cfgA ⟨(47 / 8), 11, log2Lo, log2Hi,
    ⟨4,
      (539963526309064522751208978045 / 10141204801825835211973625643008),
      (1079927052618129045502417956093 / 20282409603651670423947251286016)⟩,
    ⟨37,
      (506022708707986078689005334123 / 5070602400912917605986812821504),
      (2024090834831944314756021336495 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (47 / 8) ⟨2,
        (7796795533734972933434662732015 / 20282409603651670423947251286016),
        (3898397766867486466717331366009 / 10141204801825835211973625643008)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece8 : lgammaDiffOk cfgA ⟨(49 / 8), 10, log2Lo, log2Hi,
    ⟨4,
      (39460140009725338086696816199 / 5070602400912917605986812821504),
      (157840560038901352346787264799 / 20282409603651670423947251286016)⟩,
    ⟨33,
      (3715545964185607820879285081973 / 10141204801825835211973625643008),
      (7431091928371215641758570163949 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (49 / 8) ⟨3,
        (-5416676800313198968472078905805 / 20282409603651670423947251286016),
        (-2708338400156599484236039452901 / 10141204801825835211973625643008)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece9 : lgammaDiffOk cfgA ⟨(51 / 8), 10, log2Lo, log2Hi,
    ⟨4,
      (469883785660160440906038844505 / 20282409603651670423947251286016),
      (117470946415040110226509711127 / 5070602400912917605986812821504)⟩,
    ⟨34,
      (-190427648617022225239934849603 / 2535301200456458802993406410752),
      (-1523421188936177801919478796821 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (51 / 8) ⟨3,
        (-4605272217347008507880700715919 / 20282409603651670423947251286016),
        (-1151318054336752126970175178979 / 5070602400912917605986812821504)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece10 : lgammaDiffOk cfgA ⟨(53 / 8), 10, log2Lo, log2Hi,
    ⟨4,
      (777198901322680523450135614811 / 20282409603651670423947251286016),
      (388599450661340261725067807407 / 10141204801825835211973625643008)⟩,
    ⟨34,
      (3445270881691244700003603570377 / 20282409603651670423947251286016),
      (861317720422811175000900892595 / 5070602400912917605986812821504)⟩⟩
    (fitExpr (53 / 8) ⟨3,
        (-3825083353668555522976690708677 / 20282409603651670423947251286016),
        (-1912541676834277761488345354337 / 10141204801825835211973625643008)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece11 : lgammaDiffOk cfgA ⟨(55 / 8), 10, log2Lo, log2Hi,
    ⟨4,
      (539963526309064522751208978045 / 10141204801825835211973625643008),
      (1079927052618129045502417956093 / 20282409603651670423947251286016)⟩,
    ⟨35,
      (-1443176174725757154669660348881 / 5070602400912917605986812821504),
      (-5772704698903028618678641395521 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (55 / 8) ⟨3,
        (-768449277301893150883082254661 / 5070602400912917605986812821504),
        (-3073797109207572603532329018641 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece12 : lgammaDiffOk cfgA ⟨(57 / 8), 9, log2Lo, log2Hi,
    ⟨4,
      (39460140009725338086696816199 / 5070602400912917605986812821504),
      (157840560038901352346787264799 / 20282409603651670423947251286016)⟩,
    ⟨31,
      (-605463151524349283830783769511 / 10141204801825835211973625643008),
      (-1210926303048698567661567539019 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (57 / 8) ⟨3,
        (-1174674163807568563787981317729 / 10141204801825835211973625643008),
        (-2349348327615137127575962635455 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece13 : lgammaDiffOk cfgA ⟨(59 / 8), 9, log2Lo, log2Hi,
    ⟨4,
      (469883785660160440906038844505 / 20282409603651670423947251286016),
      (117470946415040110226509711127 / 5070602400912917605986812821504)⟩,
    ⟨31,
      (3081851028410830705961221919093 / 20282409603651670423947251286016),
      (385231378551353838245152739887 / 2535301200456458802993406410752)⟩⟩
    (fitExpr (59 / 8) ⟨3,
        (-1649885578876030500823603732749 / 20282409603651670423947251286016),
        (-824942789438015250411801866373 / 10141204801825835211973625643008)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece14 : lgammaDiffOk cfgA ⟨(61 / 8), 9, log2Lo, log2Hi,
    ⟨4,
      (777198901322680523450135614811 / 20282409603651670423947251286016),
      (388599450661340261725067807407 / 10141204801825835211973625643008)⟩,
    ⟨31,
      (7270354235359800222980294279053 / 20282409603651670423947251286016),
      (454397139709987513936268392441 / 1267650600228229401496703205376)⟩⟩
    (fitExpr (61 / 8) ⟨3,
        (-243435662072314606377676675113 / 5070602400912917605986812821504),
        (-973742648289258425510706700449 / 20282409603651670423947251286016)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_piece15 : lgammaDiffOk cfgA ⟨(63 / 8), 9, log2Lo, log2Hi,
    ⟨4,
      (539963526309064522751208978045 / 10141204801825835211973625643008),
      (1079927052618129045502417956093 / 20282409603651670423947251286016)⟩,
    ⟨32,
      (-1349453794847728007573156188441 / 10141204801825835211973625643008),
      (-2698907589695456015146312376879 / 20282409603651670423947251286016)⟩⟩
    (fitExpr (63 / 8) ⟨3,
        (-319414626612320576868098250473 / 20282409603651670423947251286016),
        (-159707313306160288434049125235 / 10141204801825835211973625643008)⟩
      log2Lo log2Hi c0Lo stirLoList) (1 / 2 ^ 64) 0 = true := by
  decide +kernel

theorem smallA_cover : ∀ x : ℝ, (4 : ℝ) ≤ x → x ≤ (4 : ℝ) + 2 * ((1 : ℝ) / 8) * 16 →
    |lgamma x - fit c0Lo stirLoList x| ≤ 1 / 2 ^ 64 := by
  refine cover_pieces (K := 16) (by norm_num) (lo := (4 : ℝ)) (r := ((1 : ℝ) / 8))
    (by norm_num) (fun x => |lgamma x - fit c0Lo stirLoList x| ≤ 1 / 2 ^ 64) ?_
  intro j hj t ht
  interval_cases j
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece0 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece1 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece2 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece3 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece4 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece5 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece6 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece7 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece8 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece9 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece10 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece11 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece12 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece13 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece14 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := fit_piece cfgA cfgA_pi _ _ c0Lo stirLoList _ _ smallA_piece15 t
      (by simp only [cfgA]; push_cast; exact ht)
    convert hb using 4 <;> norm_num

/-- The fit for `x ≤ 11.5` is within `2 ^ -64` of `lgamma` on `[4, 8]`. -/
theorem fit_small_lo {x : ℝ} (h1 : 4 ≤ x) (h2 : x ≤ 8) :
    |lgamma x - fit c0Lo stirLoList x| ≤ 1 / 2 ^ 64 :=
  smallA_cover x h1 (by norm_num; linarith)

#print axioms fit_small_lo

end Library.Numerics.Float64.Tgamma.TgammaAsymFit
