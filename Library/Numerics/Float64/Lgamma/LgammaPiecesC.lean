import Library.Numerics.Float64.Lgamma.LgammaPieceBase

/-!
Relative bounds on the pieces 9, 11, 12 of `cr_lgamma`'s piecewise polynomial on `[0.5, 8.29541]`
(`LgammaPieceBase`): on piece `j` widened by `2 ^ -50` at each end,
`|lgamma x - P_j (x - off j)| ≤ 2 ^ -63 |lgamma x|`.  Each piece splits into four sub-pieces, each
checked by `GammaRel.lgammaRelOk` with the Taylor model of `lgamma`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiecesC

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaRel LgammaPieceBase

theorem p9_0 : lgammaRelOk (cfgJ 9) (sub 9 0 15
    ⟨4,
      (57537435981542566747291716035 / 1267650600228229401496703205376),
      (920598975704681067956667456563 / 20282409603651670423947251286016)⟩
    ⟨43,
      (1186762745946596498761516600155 / 5070602400912917605986812821504),
      (4747050983786385995046066400623 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 9 + rr 9 * (2 * 0 + 1) - off 9) (pieceP 9)) (-1) εin εout
    (10485599 / 134217728) 5 = true := by
  decide +kernel

theorem p9_1 : lgammaRelOk (cfgJ 9) (sub 9 1 15
    ⟨4,
      (30923692064215096276849882717 / 633825300114114700748351602688),
      (989558146054883080859196246947 / 20282409603651670423947251286016)⟩
    ⟨43,
      (7668363402752488647114491980575 / 20282409603651670423947251286016),
      (3834181701376244323557245990289 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 9 + rr 9 * (2 * 1 + 1) - off 9) (pieceP 9)) (-1) εin εout
    (66615299 / 1073741824) 3 = true := by
  decide +kernel

theorem p9_2 : lgammaRelOk (cfgJ 9) (sub 9 2 15
    ⟨4,
      (1058283652921411145267464511699 / 20282409603651670423947251286016),
      (529141826460705572633732255851 / 10141204801825835211973625643008)⟩
    ⟨44,
      (-3513590584630812873657253347353 / 20282409603651670423947251286016),
      (-1756795292315406436828626673675 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 9 + rr 9 * (2 * 2 + 1) - off 9) (pieceP 9)) (-1) εin εout
    (46848499 / 1073741824) 3 = true := by
  decide +kernel

theorem p9_3 : lgammaRelOk (cfgJ 9) (sub 9 3 15
    ⟨4,
      (17605891788501510790536716215 / 316912650057057350374175801344),
      (1126777074464096690594349837763 / 20282409603651670423947251286016)⟩
    ⟨44,
      (-84942269988525924419818570323 / 2535301200456458802993406410752),
      (-679538159908207395358548562581 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 9 + rr 9 * (2 * 3 + 1) - off 9) (pieceP 9)) (-1) εin εout
    (24680069 / 1073741824) 5 = true := by
  decide +kernel

/-- Piece 9: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 9, border 10]` widened
by `2 ^ -50` at each end. -/
theorem piece9 : ∀ x : ℝ, (border 9 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (9 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 9) (x - off 9)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 9 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 9 0 15 _ _ _ _ _ p9_0 t ht using 3 <;> norm_num
  · convert sub_bound 9 1 15 _ _ _ _ _ p9_1 t ht using 3 <;> norm_num
  · convert sub_bound 9 2 15 _ _ _ _ _ p9_2 t ht using 3 <;> norm_num
  · convert sub_bound 9 3 15 _ _ _ _ _ p9_3 t ht using 3 <;> norm_num

theorem p11_0 : lgammaRelOk (cfgJ 11) (sub 11 0 14
    ⟨4,
      (49026007680790258365149636559 / 2535301200456458802993406410752),
      (392208061446322066921197092475 / 20282409603651670423947251286016)⟩
    ⟨41,
      (1805158291767319872479773030437 / 10141204801825835211973625643008),
      (3610316583534639744959546060877 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 11 + rr 11 * (2 * 0 + 1) - off 11) (pieceP 11)) (1) εin εout
    (145003883 / 1073741824) 5 = true := by
  decide +kernel

theorem p11_1 : lgammaRelOk (cfgJ 11) (sub 11 1 14
    ⟨4,
      (497496558579137975677292053875 / 20282409603651670423947251286016),
      (248748279289568987838646026939 / 10141204801825835211973625643008)⟩
    ⟨41,
      (7285604571372346822813906865237 / 20282409603651670423947251286016),
      (910700571421543352851738358155 / 2535301200456458802993406410752)⟩)
    (PolyBound.shift (lo 11 + rr 11 * (2 * 1 + 1) - off 11) (pieceP 11)) (1) εin εout
    (6242335 / 33554432) 3 = true := by
  decide +kernel

theorem p11_2 : lgammaRelOk (cfgJ 11) (sub 11 2 14
    ⟨4,
      (602241311527998308100383828861 / 20282409603651670423947251286016),
      (4705010246312486782034248663 / 158456325028528675187087900672)⟩
    ⟨42,
      (-3164047532903322079656030106701 / 20282409603651670423947251286016),
      (-1582023766451661039828015053349 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 11 + rr 11 * (2 * 2 + 1) - off 11) (pieceP 11)) (1) εin εout
    (258546079 / 1073741824) 3 = true := by
  decide +kernel

theorem p11_3 : lgammaRelOk (cfgJ 11) (sub 11 3 14
    ⟨4,
      (706447907595681023930792765761 / 20282409603651670423947251286016),
      (176611976898920255982698191441 / 5070602400912917605986812821504)⟩
    ⟨42,
      (381811979548170063980514574973 / 20282409603651670423947251286016),
      (2982906090220078624847770117 / 158456325028528675187087900672)⟩)
    (PolyBound.shift (lo 11 + rr 11 * (2 * 3 + 1) - off 11) (pieceP 11)) (1) εin εout
    (321207975 / 1073741824) 5 = true := by
  decide +kernel

/-- Piece 11: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 11, border 12]` widened
by `2 ^ -50` at each end. -/
theorem piece11 : ∀ x : ℝ, (border 11 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (11 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 11) (x - off 11)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 11 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 11 0 14 _ _ _ _ _ p11_0 t ht using 3 <;> norm_num
  · convert sub_bound 11 1 14 _ _ _ _ _ p11_1 t ht using 3 <;> norm_num
  · convert sub_bound 11 2 14 _ _ _ _ _ p11_2 t ht using 3 <;> norm_num
  · convert sub_bound 11 3 14 _ _ _ _ _ p11_3 t ht using 3 <;> norm_num

theorem p12_0 : lgammaRelOk (cfgJ 12) (sub 12 0 14
    ⟨4,
      (821836588852962782517047284397 / 20282409603651670423947251286016),
      (51364786803310173907315455275 / 1267650600228229401496703205376)⟩
    ⟨42,
      (2129293030402243122402582712363 / 10141204801825835211973625643008),
      (4258586060804486244805165424729 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 12 + rr 12 * (2 * 0 + 1) - off 12) (pieceP 12)) (1) εin εout
    (387583941 / 1073741824) 5 = true := by
  decide +kernel

theorem p12_1 : lgammaRelOk (cfgJ 12) (sub 12 1 14
    ⟨4,
      (948214477002275186865540318273 / 20282409603651670423947251286016),
      (237053619250568796716385079569 / 5070602400912917605986812821504)⟩
    ⟨43,
      (-2805551591818212213371664511119 / 10141204801825835211973625643008),
      (-5611103183636424426743329022235 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 12 + rr 12 * (2 * 1 + 1) - off 12) (pieceP 12)) (1) εin εout
    (236931903 / 536870912) 3 = true := by
  decide +kernel

theorem p12_2 : lgammaRelOk (cfgJ 12) (sub 12 2 14
    ⟨4,
      (1073809789427545636047231868417 / 20282409603651670423947251286016),
      (268452447356886409011807967105 / 5070602400912917605986812821504)⟩
    ⟨43,
      (-752105982444801107680946315493 / 10141204801825835211973625643008),
      (-1504211964889602215361892630983 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 12 + rr 12 * (2 * 2 + 1) - off 12) (pieceP 12)) (1) εin εout
    (282635135 / 536870912) 3 = true := by
  decide +kernel

theorem p12_3 : lgammaRelOk (cfgJ 12) (sub 12 3 14
    ⟨4,
      (1198632158473264527426989679569 / 20282409603651670423947251286016),
      (299658039618316131856747419893 / 5070602400912917605986812821504)⟩
    ⟨43,
      (2524568126997128297840596819367 / 20282409603651670423947251286016),
      (1262284063498564148920298409685 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 12 + rr 12 * (2 * 3 + 1) - off 12) (pieceP 12)) (1) εin εout
    (330789725 / 536870912) 5 = true := by
  decide +kernel

/-- Piece 12: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 12, border 13]` widened
by `2 ^ -50` at each end. -/
theorem piece12 : ∀ x : ℝ, (border 12 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (12 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 12) (x - off 12)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 12 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 12 0 14 _ _ _ _ _ p12_0 t ht using 3 <;> norm_num
  · convert sub_bound 12 1 14 _ _ _ _ _ p12_1 t ht using 3 <;> norm_num
  · convert sub_bound 12 2 14 _ _ _ _ _ p12_2 t ht using 3 <;> norm_num
  · convert sub_bound 12 3 14 _ _ _ _ _ p12_3 t ht using 3 <;> norm_num

#print axioms piece9
#print axioms piece11
#print axioms piece12

end Library.Numerics.Float64.Lgamma.LgammaPiecesC
