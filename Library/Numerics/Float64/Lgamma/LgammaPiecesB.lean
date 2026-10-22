import Library.Numerics.Float64.Lgamma.LgammaPieceBase

/-!
Relative bounds on the pieces 5, 6, 7, 8 of `cr_lgamma`'s piecewise polynomial on `[0.5, 8.29541]`
(`LgammaPieceBase`): on piece `j` widened by `2 ^ -50` at each end,
`|lgamma x - P_j (x - off j)| ≤ 2 ^ -63 |lgamma x|`.  Each piece splits into four sub-pieces, each
checked by `GammaRel.lgammaRelOk` with the Taylor model of `lgamma`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiecesB

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaRel LgammaPieceBase

theorem p5_0 : lgammaRelOk (cfgJ 5) (sub 5 0 15
    ⟨4,
      (51188969029407294063051703587 / 20282409603651670423947251286016),
      (25594484514703647031525851795 / 10141204801825835211973625643008)⟩
    ⟨40,
      (6212109513232437407339467194953 / 20282409603651670423947251286016),
      (1553027378308109351834866798739 / 5070602400912917605986812821504)⟩)
    (PolyBound.shift (lo 5 + rr 5 * (2 * 0 + 1) - off 5) (pieceP 5)) (-1) εin εout
    (14185709 / 1073741824) 6 = true := by
  decide +kernel

theorem p5_1 : lgammaRelOk (cfgJ 5) (sub 5 1 15
    ⟨4,
      (46444382778498254076853575943 / 10141204801825835211973625643008),
      (92888765556996508153707151889 / 20282409603651670423947251286016)⟩
    ⟨41,
      (-5682508315457042783104846848015 / 20282409603651670423947251286016),
      (-1420627078864260695776211712003 / 5070602400912917605986812821504)⟩)
    (PolyBound.shift (lo 5 + rr 5 * (2 * 1 + 1) - off 5) (pieceP 5)) (-1) εin εout
    (32177611 / 1073741824) 3 = true := by
  decide +kernel

theorem p5_2 : lgammaRelOk (cfgJ 5) (sub 5 2 15
    ⟨4,
      (134503004897000943889683356253 / 20282409603651670423947251286016),
      (4203218903031279496552604883 / 633825300114114700748351602688)⟩
    ⟨41,
      (-887458243135136465277779257357 / 5070602400912917605986812821504),
      (-3549832972540545861111117029425 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 5 + rr 5 * (2 * 2 + 1) - off 5) (pieceP 5)) (-1) εin εout
    (48410549 / 1073741824) 3 = true := by
  decide +kernel

theorem p5_3 : lgammaRelOk (cfgJ 5) (sub 5 3 15
    ⟨4,
      (5501001169159028721240412515 / 633825300114114700748351602688),
      (176032037413088919079693200483 / 20282409603651670423947251286016)⟩
    ⟨41,
      (-723584431017662403419711034845 / 10141204801825835211973625643008),
      (-1447168862035324806839422069687 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 5 + rr 5 * (2 * 3 + 1) - off 5) (pieceP 5)) (-1) εin εout
    (31480303 / 536870912) 5 = true := by
  decide +kernel

/-- Piece 5: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 5, border 6]` widened
by `2 ^ -50` at each end. -/
theorem piece5 : ∀ x : ℝ, (border 5 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (5 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 5) (x - off 5)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 5 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 5 0 15 _ _ _ _ _ p5_0 t ht using 3 <;> norm_num
  · convert sub_bound 5 1 15 _ _ _ _ _ p5_1 t ht using 3 <;> norm_num
  · convert sub_bound 5 2 15 _ _ _ _ _ p5_2 t ht using 3 <;> norm_num
  · convert sub_bound 5 3 15 _ _ _ _ _ p5_3 t ht using 3 <;> norm_num

theorem p6_0 : lgammaRelOk (cfgJ 6) (sub 6 0 15
    ⟨4,
      (13870310262217477612014259859 / 1267650600228229401496703205376),
      (221924964195479641792228157747 / 20282409603651670423947251286016)⟩
    ⟨41,
      (847984226288881722931276483225 / 20282409603651670423947251286016),
      (211996056572220430732819120807 / 5070602400912917605986812821504)⟩)
    (PolyBound.shift (lo 6 + rr 6 * (2 * 0 + 1) - off 6) (pieceP 6)) (-1) εin εout
    (75897949 / 1073741824) 5 = true := by
  decide +kernel

theorem p6_1 : lgammaRelOk (cfgJ 6) (sub 6 1 15
    ⟨4,
      (272152032096975354518619176745 / 20282409603651670423947251286016),
      (68038008024243838629654794187 / 5070602400912917605986812821504)⟩
    ⟨41,
      (3327227559436383308899900144005 / 20282409603651670423947251286016),
      (415903444929547913612487518001 / 2535301200456458802993406410752)⟩)
    (PolyBound.shift (lo 6 + rr 6 * (2 * 1 + 1) - off 6) (pieceP 6)) (-1) εin εout
    (89539203 / 1073741824) 3 = true := by
  decide +kernel

theorem p6_2 : lgammaRelOk (cfgJ 6) (sub 6 2 15
    ⟨4,
      (322255025601549330612338964513 / 20282409603651670423947251286016),
      (80563756400387332653084741129 / 5070602400912917605986812821504)⟩
    ⟨41,
      (5767946757171633451971918503215 / 20282409603651670423947251286016),
      (2883973378585816725985959251609 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 6 + rr 6 * (2 * 2 + 1) - off 6) (pieceP 6)) (-1) εin εout
    (50501285 / 536870912) 3 = true := by
  decide +kernel

theorem p6_3 : lgammaRelOk (cfgJ 6) (sub 6 3 15
    ⟨4,
      (372234556193392736567788074227 / 20282409603651670423947251286016),
      (186117278096696368283894037115 / 10141204801825835211973625643008)⟩
    ⟨41,
      (2042981919149800937495421916725 / 5070602400912917605986812821504),
      (8171927676599203749981687666903 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 6 + rr 6 * (2 * 3 + 1) - off 6) (pieceP 6)) (-1) εin εout
    (55193025 / 536870912) 5 = true := by
  decide +kernel

/-- Piece 6: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 6, border 7]` widened
by `2 ^ -50` at each end. -/
theorem piece6 : ∀ x : ℝ, (border 6 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (6 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 6) (x - off 6)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 6 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 6 0 15 _ _ _ _ _ p6_0 t ht using 3 <;> norm_num
  · convert sub_bound 6 1 15 _ _ _ _ _ p6_1 t ht using 3 <;> norm_num
  · convert sub_bound 6 2 15 _ _ _ _ _ p6_2 t ht using 3 <;> norm_num
  · convert sub_bound 6 3 15 _ _ _ _ _ p6_3 t ht using 3 <;> norm_num

theorem p7_0 : lgammaRelOk (cfgJ 7) (sub 7 0 15
    ⟨4,
      (426130729365879733451285761279 / 20282409603651670423947251286016),
      (213065364682939866725642880641 / 10141204801825835211973625643008)⟩
    ⟨42,
      (-3327187418544911616136413100343 / 20282409603651670423947251286016),
      (-831796854636227904034103275085 / 5070602400912917605986812821504)⟩)
    (PolyBound.shift (lo 7 + rr 7 * (2 * 0 + 1) - off 7) (pieceP 7)) (-1) εin εout
    (117779635 / 1073741824) 5 = true := by
  decide +kernel

theorem p7_1 : lgammaRelOk (cfgJ 7) (sub 7 1 15
    ⟨4,
      (120978017577928632338078231945 / 5070602400912917605986812821504),
      (483912070311714529352312927783 / 20282409603651670423947251286016)⟩
    ⟨42,
      (-154777827066241566448727270313 / 5070602400912917605986812821504),
      (-619111308264966265794909081249 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 7 + rr 7 * (2 * 1 + 1) - off 7) (pieceP 7)) (-1) εin εout
    (15497743 / 134217728) 3 = true := by
  decide +kernel

theorem p7_2 : lgammaRelOk (cfgJ 7) (sub 7 2 15
    ⟨4,
      (270764634481659705080247030523 / 10141204801825835211973625643008),
      (541529268963319410160494061049 / 20282409603651670423947251286016)⟩
    ⟨42,
      (2045928070624246161035844533049 / 20282409603651670423947251286016),
      (511482017656061540258961133263 / 5070602400912917605986812821504)⟩)
    (PolyBound.shift (lo 7 + rr 7 * (2 * 2 + 1) - off 7) (pieceP 7)) (-1) εin εout
    (3991483 / 33554432) 3 = true := by
  decide +kernel

theorem p7_3 : lgammaRelOk (cfgJ 7) (sub 7 3 15
    ⟨4,
      (598983255253771628641525339017 / 20282409603651670423947251286016),
      (149745813813442907160381334755 / 5070602400912917605986812821504)⟩
    ⟨42,
      (2334960920494748429817161641647 / 10141204801825835211973625643008),
      (4669921840989496859634323283297 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 7 + rr 7 * (2 * 3 + 1) - off 7) (pieceP 7)) (-1) εin εout
    (128276693 / 1073741824) 5 = true := by
  decide +kernel

/-- Piece 7: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 7, border 8]` widened
by `2 ^ -50` at each end. -/
theorem piece7 : ∀ x : ℝ, (border 7 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (7 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 7) (x - off 7)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 7 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 7 0 15 _ _ _ _ _ p7_0 t ht using 3 <;> norm_num
  · convert sub_bound 7 1 15 _ _ _ _ _ p7_1 t ht using 3 <;> norm_num
  · convert sub_bound 7 2 15 _ _ _ _ _ p7_2 t ht using 3 <;> norm_num
  · convert sub_bound 7 3 15 _ _ _ _ _ p7_3 t ht using 3 <;> norm_num

theorem p8_0 : lgammaRelOk (cfgJ 8) (sub 8 0 15
    ⟨4,
      (41257978554581021746725958937 / 1267650600228229401496703205376),
      (660127656873296347947615342995 / 20282409603651670423947251286016)⟩
    ⟨42,
      (7427415164521472398694728105659 / 20282409603651670423947251286016),
      (3713707582260736199347364052831 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 8 + rr 8 * (2 * 0 + 1) - off 8) (pieceP 8)) (-1) εin εout
    (62354475 / 536870912) 5 = true := by
  decide +kernel

theorem p8_1 : lgammaRelOk (cfgJ 8) (sub 8 1 15
    ⟨4,
      (362464349127863033670141326063 / 10141204801825835211973625643008),
      (724928698255726067340282652129 / 20282409603651670423947251286016)⟩
    ⟨43,
      (-3746495671654238155329555949271 / 20282409603651670423947251286016),
      (-936623917913559538832388987317 / 5070602400912917605986812821504)⟩)
    (PolyBound.shift (lo 8 + rr 8 * (2 * 1 + 1) - off 8) (pieceP 8)) (-1) εin εout
    (14811421 / 134217728) 3 = true := by
  decide +kernel

theorem p8_2 : lgammaRelOk (cfgJ 8) (sub 8 2 15
    ⟨4,
      (12336302554873077576583426521 / 316912650057057350374175801344),
      (789523363511876964901339297347 / 20282409603651670423947251286016)⟩
    ⟨43,
      (-907633085945421173028522651747 / 20282409603651670423947251286016),
      (-28363533935794411657141332867 / 633825300114114700748351602688)⟩)
    (PolyBound.shift (lo 8 + rr 8 * (2 * 2 + 1) - off 8) (pieceP 8)) (-1) εin εout
    (109737949 / 1073741824) 3 = true := by
  decide +kernel

theorem p8_3 : lgammaRelOk (cfgJ 8) (sub 8 3 15
    ⟨4,
      (853912962988872522428005648967 / 20282409603651670423947251286016),
      (426956481494436261214002824485 / 10141204801825835211973625643008)⟩
    ⟨43,
      (1887382211749285808563099548433 / 20282409603651670423947251286016),
      (471845552937321452140774887109 / 5070602400912917605986812821504)⟩)
    (PolyBound.shift (lo 8 + rr 8 * (2 * 3 + 1) - off 8) (pieceP 8)) (-1) εin εout
    (12319201 / 134217728) 5 = true := by
  decide +kernel

/-- Piece 8: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 8, border 9]` widened
by `2 ^ -50` at each end. -/
theorem piece8 : ∀ x : ℝ, (border 8 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (8 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 8) (x - off 8)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 8 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 8 0 15 _ _ _ _ _ p8_0 t ht using 3 <;> norm_num
  · convert sub_bound 8 1 15 _ _ _ _ _ p8_1 t ht using 3 <;> norm_num
  · convert sub_bound 8 2 15 _ _ _ _ _ p8_2 t ht using 3 <;> norm_num
  · convert sub_bound 8 3 15 _ _ _ _ _ p8_3 t ht using 3 <;> norm_num

#print axioms piece5
#print axioms piece6
#print axioms piece7
#print axioms piece8

end Library.Numerics.Float64.Lgamma.LgammaPiecesB
