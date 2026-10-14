import Verified.Examples.LgammaPieceBase

/-!
Relative bounds on the pieces 16, 17, 18 of `cr_lgamma`'s piecewise polynomial on `[0.5, 8.29541]`
(`LgammaPieceBase`): on piece `j` widened by `2 ^ -50` at each end,
`|lgamma x - P_j (x - off j)| ≤ 2 ^ -63 |lgamma x|`.  Each piece splits into four sub-pieces, each
checked by `GammaRel.lgammaRelOk` with the Taylor model of `lgamma`.
-/

namespace Verified.Examples.LgammaPiecesE

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaRel LgammaPieceBase

theorem p16_0 : lgammaRelOk (cfgJ 16) (sub 16 0 12
    ⟨4,
      (625260089268066878802109645651 / 10141204801825835211973625643008),
      (1250520178536133757604219291305 / 20282409603651670423947251286016)⟩
    ⟨40,
      (-2123154695583093640574277909989 / 10141204801825835211973625643008),
      (-4246309391166187281148555819975 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 16 + rr 16 * (2 * 0 + 1) - off 16) (pieceP 16)) (1) εin εout
    (3224414889 / 1073741824) 5 = true := by
  decide +kernel

theorem p16_1 : lgammaRelOk (cfgJ 16) (sub 16 1 11
    ⟨4,
      (309719444797403969045329399765 / 20282409603651670423947251286016),
      (38714930599675496130666174971 / 2535301200456458802993406410752)⟩
    ⟨36,
      (1365125688831496253099934530423 / 20282409603651670423947251286016),
      (682562844415748126549967265213 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 16 + rr 16 * (2 * 1 + 1) - off 16) (pieceP 16)) (1) εin εout
    (448928833 / 134217728) 3 = true := by
  decide +kernel

theorem p16_2 : lgammaRelOk (cfgJ 16) (sub 16 2 11
    ⟨4,
      (593207604317502433516770942835 / 20282409603651670423947251286016),
      (296603802158751216758385471419 / 10141204801825835211973625643008)⟩
    ⟨36,
      (6843383125053894596360461711955 / 20282409603651670423947251286016),
      (3421691562526947298180230855979 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 16 + rr 16 * (2 * 2 + 1) - off 16) (pieceP 16)) (1) εin εout
    (1985202795 / 536870912) 3 = true := by
  decide +kernel

theorem p16_3 : lgammaRelOk (cfgJ 16) (sub 16 3 11
    ⟨4,
      (436393996656004094941022072759 / 10141204801825835211973625643008),
      (872787993312008189882044145521 / 20282409603651670423947251286016)⟩
    ⟨37,
      (-1883232408795148338683880120293 / 20282409603651670423947251286016),
      (-941616204397574169341940060145 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 16 + rr 16 * (2 * 3 + 1) - off 16) (pieceP 16)) (1) εin εout
    (4360780589 / 1073741824) 5 = true := by
  decide +kernel

/-- Piece 16: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 16, border 17]` widened
by `2 ^ -50` at each end. -/
theorem piece16 : ∀ x : ℝ, (border 16 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (16 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 16) (x - off 16)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 16 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 16 0 12 _ _ _ _ _ p16_0 t ht using 3 <;> norm_num
  · convert sub_bound 16 1 11 _ _ _ _ _ p16_1 t ht using 3 <;> norm_num
  · convert sub_bound 16 2 11 _ _ _ _ _ p16_2 t ht using 3 <;> norm_num
  · convert sub_bound 16 3 11 _ _ _ _ _ p16_3 t ht using 3 <;> norm_num

theorem p17_0 : lgammaRelOk (cfgJ 17) (sub 17 0 11
    ⟨4,
      (1178483993811747055090304763121 / 20282409603651670423947251286016),
      (294620998452936763772576190781 / 5070602400912917605986812821504)⟩
    ⟨37,
      (60480302985018535618173092129 / 316912650057057350374175801344),
      (3870739391041186279563077896259 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 17 + rr 17 * (2 * 0 + 1) - off 17) (pieceP 17)) (1) εin εout
    (4762046385 / 1073741824) 5 = true := by
  decide +kernel

theorem p17_1 : lgammaRelOk (cfgJ 17) (sub 17 1 10
    ⟨4,
      (296799644035769380565397864607 / 20282409603651670423947251286016),
      (148399822017884690282698932305 / 10141204801825835211973625643008)⟩
    ⟨34,
      (-2173537565243962460945514455645 / 10141204801825835211973625643008),
      (-4347075130487924921891028911287 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 17 + rr 17 * (2 * 1 + 1) - off 17) (pieceP 17)) (1) εin εout
    (1316270041 / 268435456) 3 = true := by
  decide +kernel

theorem p17_2 : lgammaRelOk (cfgJ 17) (sub 17 2 10
    ⟨4,
      (320976568345543194934145716769 / 10141204801825835211973625643008),
      (641953136691086389868291433541 / 20282409603651670423947251286016)⟩
    ⟨34,
      (79096281256531045195308358761 / 1267650600228229401496703205376),
      (1265540500104496723124933740179 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 17 + rr 17 * (2 * 2 + 1) - off 17) (pieceP 17)) (1) εin εout
    (1445707455 / 268435456) 3 = true := by
  decide +kernel

theorem p17_3 : lgammaRelOk (cfgJ 17) (sub 17 3 10
    ⟨4,
      (490665583522067995539686044501 / 10141204801825835211973625643008),
      (981331167044135991079372089005 / 20282409603651670423947251286016)⟩
    ⟨34,
      (3357562463565124132314244227505 / 10141204801825835211973625643008),
      (6715124927130248264628488455013 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 17 + rr 17 * (2 * 3 + 1) - off 17) (pieceP 17)) (1) εin εout
    (98665629 / 16777216) 5 = true := by
  decide +kernel

/-- Piece 17: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 17, border 18]` widened
by `2 ^ -50` at each end. -/
theorem piece17 : ∀ x : ℝ, (border 17 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (17 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 17) (x - off 17)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 17 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 17 0 11 _ _ _ _ _ p17_0 t ht using 3 <;> norm_num
  · convert sub_bound 17 1 10 _ _ _ _ _ p17_1 t ht using 3 <;> norm_num
  · convert sub_bound 17 2 10 _ _ _ _ _ p17_2 t ht using 3 <;> norm_num
  · convert sub_bound 17 3 10 _ _ _ _ _ p17_3 t ht using 3 <;> norm_num

theorem p18_0 : lgammaRelOk (cfgJ 18) (sub 18 0 10
    ⟨4,
      (168995443679655277942085204085 / 2535301200456458802993406410752),
      (1351963549437242223536681632683 / 20282409603651670423947251286016)⟩
    ⟨35,
      (-366585730337093275788940511833 / 5070602400912917605986812821504),
      (-1466342921348373103155762047329 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 18 + rr 18 * (2 * 0 + 1) - off 18) (pieceP 18)) (1) εin εout
    (3429879483 / 536870912) 5 = true := by
  decide +kernel

theorem p18_1 : lgammaRelOk (cfgJ 18) (sub 18 1 9
    ⟨4,
      (69332647083886190853522538307 / 2535301200456458802993406410752),
      (554661176671089526828180306459 / 20282409603651670423947251286016)⟩
    ⟨31,
      (265070715730611926527432200275 / 1267650600228229401496703205376),
      (4241131451689790824438915204403 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 18 + rr 18 * (2 * 1 + 1) - off 18) (pieceP 18)) (1) εin εout
    (7543710073 / 1073741824) 3 = true := by
  decide +kernel

theorem p18_2 : lgammaRelOk (cfgJ 18) (sub 18 2 9
    ⟨4,
      (121329925069053680078047444873 / 2535301200456458802993406410752),
      (970639400552429440624379558987 / 20282409603651670423947251286016)⟩
    ⟨32,
      (-4171136477443651956366330507427 / 20282409603651670423947251286016),
      (-130348014920114123636447828357 / 633825300114114700748351602688)⟩)
    (PolyBound.shift (lo 18 + rr 18 * (2 * 2 + 1) - off 18) (pieceP 18)) (1) εin εout
    (8245856313 / 1073741824) 3 = true := by
  decide +kernel

theorem p18_3 : lgammaRelOk (cfgJ 18) (sub 18 3 9
    ⟨4,
      (689128686973614804333307757625 / 10141204801825835211973625643008),
      (1378257373947229608666615515253 / 20282409603651670423947251286016)⟩
    ⟨32,
      (648492883656421349639860415931 / 10141204801825835211973625643008),
      (1296985767312842699279720831865 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 18 + rr 18 * (2 * 3 + 1) - off 18) (pieceP 18)) (1) εin εout
    (140083257 / 16777216) 5 = true := by
  decide +kernel

/-- Piece 18: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 18, border 19]` widened
by `2 ^ -50` at each end. -/
theorem piece18 : ∀ x : ℝ, (border 18 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (18 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 18) (x - off 18)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 18 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 18 0 10 _ _ _ _ _ p18_0 t ht using 3 <;> norm_num
  · convert sub_bound 18 1 9 _ _ _ _ _ p18_1 t ht using 3 <;> norm_num
  · convert sub_bound 18 2 9 _ _ _ _ _ p18_2 t ht using 3 <;> norm_num
  · convert sub_bound 18 3 9 _ _ _ _ _ p18_3 t ht using 3 <;> norm_num

#print axioms piece16
#print axioms piece17
#print axioms piece18

end Verified.Examples.LgammaPiecesE
