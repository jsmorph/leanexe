import Library.Numerics.Float64.Lgamma.LgammaPieceBase

/-!
Relative bounds on the pieces 13, 14, 15 of `cr_lgamma`'s piecewise polynomial on `[0.5, 8.29541]`
(`LgammaPieceBase`): on piece `j` widened by `2 ^ -50` at each end,
`|lgamma x - P_j (x - off j)| ≤ 2 ^ -63 |lgamma x|`.  Each piece splits into four sub-pieces, each
checked by `GammaRel.lgammaRelOk` with the Taylor model of `lgamma`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiecesD

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaRel LgammaPieceBase

theorem p13_0 : lgammaRelOk (cfgJ 13) (sub 13 0 13
    ⟨4,
      (7077807525874607184173450445 / 1267650600228229401496703205376),
      (113244920413993714946775207123 / 20282409603651670423947251286016)⟩
    ⟨39,
      (6793810759444126281945855260951 / 20282409603651670423947251286016),
      (3396905379722063140972927630477 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 13 + rr 13 * (2 * 0 + 1) - off 13) (pieceP 13)) (1) εin εout
    (762585985 / 1073741824) 5 = true := by
  decide +kernel

theorem p13_1 : lgammaRelOk (cfgJ 13) (sub 13 1 13
    ⟨4,
      (136307419060646027679659781571 / 10141204801825835211973625643008),
      (272614838121292055359319563145 / 20282409603651670423947251286016)⟩
    ⟨40,
      (-677458903740703515796154138715 / 5070602400912917605986812821504),
      (-2709835614962814063184616554857 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 13 + rr 13 * (2 * 1 + 1) - off 13) (pieceP 13)) (1) εin εout
    (55735389 / 67108864) 3 = true := by
  decide +kernel

theorem p13_2 : lgammaRelOk (cfgJ 13) (sub 13 2 13
    ⟨4,
      (430742256402704128418761476379 / 20282409603651670423947251286016),
      (215371128201352064209380738191 / 10141204801825835211973625643008)⟩
    ⟨40,
      (873488037923412576341221098421 / 10141204801825835211973625643008),
      (1746976075846825152682442196845 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 13 + rr 13 * (2 * 2 + 1) - off 13) (pieceP 13)) (1) εin εout
    (1027330377 / 1073741824) 3 = true := by
  decide +kernel

theorem p13_3 : lgammaRelOk (cfgJ 13) (sub 13 3 13
    ⟨4,
      (146911599833139332229585523889 / 5070602400912917605986812821504),
      (587646399332557328918342095559 / 20282409603651670423947251286016)⟩
    ⟨40,
      (6110596085365936894909025426569 / 20282409603651670423947251286016),
      (1527649021341484223727256356643 / 5070602400912917605986812821504)⟩)
    (PolyBound.shift (lo 13 + rr 13 * (2 * 3 + 1) - off 13) (pieceP 13)) (1) εin εout
    (1168992763 / 1073741824) 5 = true := by
  decide +kernel

/-- Piece 13: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 13, border 14]` widened
by `2 ^ -50` at each end. -/
theorem piece13 : ∀ x : ℝ, (border 13 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (13 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 13) (x - off 13)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 13 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 13 0 13 _ _ _ _ _ p13_0 t ht using 3 <;> norm_num
  · convert sub_bound 13 1 13 _ _ _ _ _ p13_1 t ht using 3 <;> norm_num
  · convert sub_bound 13 2 13 _ _ _ _ _ p13_2 t ht using 3 <;> norm_num
  · convert sub_bound 13 3 13 _ _ _ _ _ p13_3 t ht using 3 <;> norm_num

theorem p14_0 : lgammaRelOk (cfgJ 14) (sub 14 0 13
    ⟨4,
      (760139803358917120436380000825 / 20282409603651670423947251286016),
      (190034950839729280109095000207 / 5070602400912917605986812821504)⟩
    ⟨41,
      (-3215121896777151146184017225807 / 20282409603651670423947251286016),
      (-803780474194287786546004306451 / 5070602400912917605986812821504)⟩)
    (PolyBound.shift (lo 14 + rr 14 * (2 * 0 + 1) - off 14) (pieceP 14)) (1) εin εout
    (1316491973 / 1073741824) 5 = true := by
  decide +kernel

theorem p14_1 : lgammaRelOk (cfgJ 14) (sub 14 1 13
    ⟨4,
      (473908798679143194327200703955 / 10141204801825835211973625643008),
      (947817597358286388654401407913 / 20282409603651670423947251286016)⟩
    ⟨41,
      (1861945909670614114907118335093 / 20282409603651670423947251286016),
      (232743238708826764363389791887 / 2535301200456458802993406410752)⟩)
    (PolyBound.shift (lo 14 + rr 14 * (2 * 1 + 1) - off 14) (pieceP 14)) (1) εin εout
    (46983441 / 33554432) 3 = true := by
  decide +kernel

theorem p14_2 : lgammaRelOk (cfgJ 14) (sub 14 2 13
    ⟨4,
      (1133774675641499577392474656863 / 20282409603651670423947251286016),
      (566887337820749788696237328433 / 10141204801825835211973625643008)⟩
    ⟨41,
      (3410849988308704521250212077145 / 10141204801825835211973625643008),
      (6821699976617409042500424154293 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 14 + rr 14 * (2 * 2 + 1) - off 14) (pieceP 14)) (1) εin εout
    (849169241 / 536870912) 3 = true := by
  decide +kernel

theorem p14_3 : lgammaRelOk (cfgJ 14) (sub 14 3 13
    ⟨4,
      (1318042304377923973704549602953 / 20282409603651670423947251286016),
      (329510576094480993426137400739 / 5070602400912917605986812821504)⟩
    ⟨42,
      (-2388282487383875981879638949357 / 20282409603651670423947251286016),
      (-1194141243691937990939819474677 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 14 + rr 14 * (2 * 3 + 1) - off 14) (pieceP 14)) (1) εin εout
    (950368807 / 536870912) 5 = true := by
  decide +kernel

/-- Piece 14: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 14, border 15]` widened
by `2 ^ -50` at each end. -/
theorem piece14 : ∀ x : ℝ, (border 14 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (14 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 14) (x - off 14)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 14 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 14 0 13 _ _ _ _ _ p14_0 t ht using 3 <;> norm_num
  · convert sub_bound 14 1 13 _ _ _ _ _ p14_1 t ht using 3 <;> norm_num
  · convert sub_bound 14 2 13 _ _ _ _ _ p14_2 t ht using 3 <;> norm_num
  · convert sub_bound 14 3 13 _ _ _ _ _ p14_3 t ht using 3 <;> norm_num

theorem p15_0 : lgammaRelOk (cfgJ 15) (sub 15 0 12
    ⟨4,
      (154392994366199015918310410111 / 10141204801825835211973625643008),
      (308785988732398031836620820225 / 20282409603651670423947251286016)⟩
    ⟨38,
      (1277432583425098379062922822921 / 10141204801825835211973625643008),
      (2554865166850196758125845645845 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 15 + rr 15 * (2 * 0 + 1) - off 15) (pieceP 15)) (1) εin εout
    (1055169591 / 536870912) 5 = true := by
  decide +kernel

theorem p15_1 : lgammaRelOk (cfgJ 15) (sub 15 1 12
    ⟨4,
      (135516502043646385718312363133 / 5070602400912917605986812821504),
      (542066008174585542873249452535 / 20282409603651670423947251286016)⟩
    ⟨38,
      (7946951904374687796981582506137 / 20282409603651670423947251286016),
      (1986737976093671949245395626535 / 5070602400912917605986812821504)⟩)
    (PolyBound.shift (lo 15 + rr 15 * (2 * 1 + 1) - off 15) (pieceP 15)) (1) εin εout
    (2374706251 / 1073741824) 3 = true := by
  decide +kernel

theorem p15_2 : lgammaRelOk (cfgJ 15) (sub 15 2 12
    ⟨4,
      (772693416136349358619289835023 / 20282409603651670423947251286016),
      (386346708068174679309644917513 / 10141204801825835211973625643008)⟩
    ⟨39,
      (-213982731425998214735333274725 / 5070602400912917605986812821504),
      (-855930925703992858941333098897 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 15 + rr 15 * (2 * 2 + 1) - off 15) (pieceP 15)) (1) εin εout
    (1324400529 / 536870912) 3 = true := by
  decide +kernel

theorem p15_3 : lgammaRelOk (cfgJ 15) (sub 15 3 12
    ⟨4,
      (250181965084487090312217912485 / 5070602400912917605986812821504),
      (1000727860337948361248871649943 / 20282409603651670423947251286016)⟩
    ⟨39,
      (4271271969791873558460840351759 / 20282409603651670423947251286016),
      (2135635984895936779230420175881 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 15 + rr 15 * (2 * 3 + 1) - off 15) (pieceP 15)) (1) εin εout
    (1466086981 / 536870912) 5 = true := by
  decide +kernel

/-- Piece 15: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 15, border 16]` widened
by `2 ^ -50` at each end. -/
theorem piece15 : ∀ x : ℝ, (border 15 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (15 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 15) (x - off 15)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 15 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 15 0 12 _ _ _ _ _ p15_0 t ht using 3 <;> norm_num
  · convert sub_bound 15 1 12 _ _ _ _ _ p15_1 t ht using 3 <;> norm_num
  · convert sub_bound 15 2 12 _ _ _ _ _ p15_2 t ht using 3 <;> norm_num
  · convert sub_bound 15 3 12 _ _ _ _ _ p15_3 t ht using 3 <;> norm_num

#print axioms piece13
#print axioms piece14
#print axioms piece15

end Library.Numerics.Float64.Lgamma.LgammaPiecesD
