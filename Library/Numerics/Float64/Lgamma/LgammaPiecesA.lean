import Library.Numerics.Float64.Lgamma.LgammaPieceBase

/-!
Relative bounds on the pieces 0, 1, 2, 3 of `cr_lgamma`'s piecewise polynomial on `[0.5, 8.29541]`
(`LgammaPieceBase`): on piece `j` widened by `2 ^ -50` at each end,
`|lgamma x - P_j (x - off j)| ≤ 2 ^ -63 |lgamma x|`.  Each piece splits into four sub-pieces, each
checked by `GammaRel.lgammaRelOk` with the Taylor model of `lgamma`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiecesA

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaRel LgammaPieceBase

theorem p0_0 : lgammaRelOk (cfgJ 0) (sub 0 0 16
    ⟨4,
      (159094291240880141753556372285 / 5070602400912917605986812821504),
      (636377164963520567014225489143 / 20282409603651670423947251286016)⟩
    ⟨41,
      (6761016854074967371991403761699 / 20282409603651670423947251286016),
      (3380508427037483685995701880851 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 0 + rr 0 * (2 * 0 + 1) - off 0) (pieceP 0)) (1) εin εout
    (70977593 / 134217728) 5 = true := by
  decide +kernel

theorem p0_1 : lgammaRelOk (cfgJ 0) (sub 0 1 16
    ⟨4,
      (330431268523463292254968073721 / 10141204801825835211973625643008),
      (660862537046926584509936147445 / 20282409603651670423947251286016)⟩
    ⟨42,
      (-2709887980467225478202563347053 / 10141204801825835211973625643008),
      (-5419775960934450956405126694103 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 0 + rr 0 * (2 * 1 + 1) - off 0) (pieceP 0)) (1) εin εout
    (264584239 / 536870912) 3 = true := by
  decide +kernel

theorem p0_2 : lgammaRelOk (cfgJ 0) (sub 0 2 16
    ⟨4,
      (685318385487283463351528655895 / 20282409603651670423947251286016),
      (342659192743641731675764327949 / 10141204801825835211973625643008)⟩
    ⟨42,
      (-3577464916889090798906297068215 / 20282409603651670423947251286016),
      (-894366229222272699726574267053 / 5070602400912917605986812821504)⟩)
    (PolyBound.shift (lo 0 + rr 0 * (2 * 2 + 1) - off 0) (pieceP 0)) (1) εin εout
    (492349441 / 1073741824) 3 = true := by
  decide +kernel

theorem p0_3 : lgammaRelOk (cfgJ 0) (sub 0 3 16
    ⟨4,
      (354872390698049702050553645439 / 10141204801825835211973625643008),
      (709744781396099404101107290881 / 20282409603651670423947251286016)⟩
    ⟨42,
      (-221071503857226812563001896045 / 2535301200456458802993406410752),
      (-1768572030857814500504015168357 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 0 + rr 0 * (2 * 3 + 1) - off 0) (pieceP 0)) (1) εin εout
    (457255565 / 1073741824) 5 = true := by
  decide +kernel

/-- Piece 0: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 0, border 1]` widened
by `2 ^ -50` at each end. -/
theorem piece0 : ∀ x : ℝ, (border 0 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (0 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 0) (x - off 0)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 0 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 0 0 16 _ _ _ _ _ p0_0 t ht using 3 <;> norm_num
  · convert sub_bound 0 1 16 _ _ _ _ _ p0_1 t ht using 3 <;> norm_num
  · convert sub_bound 0 2 16 _ _ _ _ _ p0_2 t ht using 3 <;> norm_num
  · convert sub_bound 0 3 16 _ _ _ _ _ p0_3 t ht using 3 <;> norm_num

theorem p1_0 : lgammaRelOk (cfgJ 1) (sub 1 0 16
    ⟨4,
      (367857883544897964886156759449 / 10141204801825835211973625643008),
      (735715767089795929772313518901 / 20282409603651670423947251286016)⟩
    ⟨42,
      (30641569670625905572939525569 / 5070602400912917605986812821504),
      (122566278682503622291758102279 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 1 + rr 1 * (2 * 0 + 1) - off 1) (pieceP 1)) (1) εin εout
    (419582357 / 1073741824) 5 = true := by
  decide +kernel

theorem p1_1 : lgammaRelOk (cfgJ 1) (sub 1 1 16
    ⟨4,
      (381612689141066334288269482181 / 10141204801825835211973625643008),
      (763225378282132668576538964365 / 20282409603651670423947251286016)⟩
    ⟨42,
      (522947854496280183811599359163 / 5070602400912917605986812821504),
      (2091791417985120735246397436655 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 1 + rr 1 * (2 * 1 + 1) - off 1) (pieceP 1)) (1) εin εout
    (95964487 / 268435456) 3 = true := by
  decide +kernel

theorem p1_2 : lgammaRelOk (cfgJ 1) (sub 1 2 16
    ⟨4,
      (790697727936614434025265205691 / 20282409603651670423947251286016),
      (395348863968307217012632602847 / 10141204801825835211973625643008)⟩
    ⟨42,
      (4025583871539161635872940110071 / 20282409603651670423947251286016),
      (2012791935769580817936470055037 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 1 + rr 1 * (2 * 2 + 1) - off 1) (pieceP 1)) (1) εin εout
    (174984331 / 536870912) 3 = true := by
  decide +kernel

theorem p1_3 : lgammaRelOk (cfgJ 1) (sub 1 3 16
    ⟨4,
      (818132916857599573050106050271 / 20282409603651670423947251286016),
      (409066458428799786525053025137 / 10141204801825835211973625643008)⟩
    ⟨42,
      (5926002143044450037614148602469 / 20282409603651670423947251286016),
      (740750267880556254701768575309 / 2535301200456458802993406410752)⟩)
    (PolyBound.shift (lo 1 + rr 1 * (2 * 3 + 1) - off 1) (pieceP 1)) (1) εin εout
    (158905957 / 536870912) 5 = true := by
  decide +kernel

/-- Piece 1: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 1, border 2]` widened
by `2 ^ -50` at each end. -/
theorem piece1 : ∀ x : ℝ, (border 1 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (1 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 1) (x - off 1)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 1 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 1 0 16 _ _ _ _ _ p1_0 t ht using 3 <;> norm_num
  · convert sub_bound 1 1 16 _ _ _ _ _ p1_1 t ht using 3 <;> norm_num
  · convert sub_bound 1 2 16 _ _ _ _ _ p1_2 t ht using 3 <;> norm_num
  · convert sub_bound 1 3 16 _ _ _ _ _ p1_3 t ht using 3 <;> norm_num

theorem p2_0 : lgammaRelOk (cfgJ 2) (sub 2 0 16
    ⟨4,
      (847107991556730365901615787071 / 20282409603651670423947251286016),
      (423553995778365182950807893537 / 10141204801825835211973625643008)⟩
    ⟨42,
      (7901628587346876151724094907359 / 20282409603651670423947251286016),
      (3950814293673438075862047453681 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 2 + rr 2 * (2 * 0 + 1) - off 2) (pieceP 2)) (1) εin εout
    (283880743 / 1073741824) 5 = true := by
  decide +kernel

theorem p2_1 : lgammaRelOk (cfgJ 2) (sub 2 1 16
    ⟨4,
      (438808153922617569826259095857 / 10141204801825835211973625643008),
      (877616307845235139652518191717 / 20282409603651670423947251286016)⟩
    ⟨43,
      (-2054915851240700572194619238305 / 10141204801825835211973625643008),
      (-4109831702481401144389238476607 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 2 + rr 2 * (2 * 1 + 1) - off 2) (pieceP 2)) (1) εin εout
    (251872295 / 1073741824) 3 = true := by
  decide +kernel

theorem p2_2 : lgammaRelOk (cfgJ 2) (sub 2 2 16
    ⟨4,
      (227019700791733721690627476423 / 5070602400912917605986812821504),
      (908078803166934886762509905695 / 20282409603651670423947251286016)⟩
    ⟨43,
      (-524366102644053916137484996857 / 5070602400912917605986812821504),
      (-2097464410576215664549939987425 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 2 + rr 2 * (2 * 2 + 1) - off 2) (pieceP 2)) (1) εin εout
    (110840633 / 536870912) 3 = true := by
  decide +kernel

theorem p2_3 : lgammaRelOk (cfgJ 2) (sub 2 3 16
    ⟨4,
      (938495614954045407998862095359 / 20282409603651670423947251286016),
      (469247807477022703999431047681 / 10141204801825835211973625643008)⟩
    ⟨43,
      (-118053588998814159398835681837 / 20282409603651670423947251286016),
      (-59026794499407079699417840917 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 2 + rr 2 * (2 * 3 + 1) - off 2) (pieceP 2)) (1) εin εout
    (193212187 / 1073741824) 5 = true := by
  decide +kernel

/-- Piece 2: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 2, border 3]` widened
by `2 ^ -50` at each end. -/
theorem piece2 : ∀ x : ℝ, (border 2 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (2 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 2) (x - off 2)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 2 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 2 0 16 _ _ _ _ _ p2_0 t ht using 3 <;> norm_num
  · convert sub_bound 2 1 16 _ _ _ _ _ p2_1 t ht using 3 <;> norm_num
  · convert sub_bound 2 2 16 _ _ _ _ _ p2_2 t ht using 3 <;> norm_num
  · convert sub_bound 2 3 16 _ _ _ _ _ p2_3 t ht using 3 <;> norm_num

theorem p3_0 : lgammaRelOk (cfgJ 3) (sub 3 0 16
    ⟨4,
      (970275228223475461412761242311 / 20282409603651670423947251286016),
      (485137614111737730706380621157 / 10141204801825835211973625643008)⟩
    ⟨43,
      (59994236241791999929941734527 / 633825300114114700748351602688),
      (1919815559737343997758135504867 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 3 + rr 3 * (2 * 0 + 1) - off 3) (pieceP 3)) (1) εin εout
    (163967655 / 1073741824) 5 = true := by
  decide +kernel

theorem p3_1 : lgammaRelOk (cfgJ 3) (sub 3 1 16
    ⟨4,
      (501705587224341757607193969721 / 10141204801825835211973625643008),
      (1003411174448683515214387939445 / 20282409603651670423947251286016)⟩
    ⟨43,
      (2006762681766140712792174309145 / 10141204801825835211973625643008),
      (4013525363532281425584348618293 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 3 + rr 3 * (2 * 1 + 1) - off 3) (pieceP 3)) (1) εin εout
    (136572837 / 1073741824) 3 = true := by
  decide +kernel

theorem p3_2 : lgammaRelOk (cfgJ 3) (sub 3 2 16
    ⟨4,
      (518246536913603154884042936201 / 10141204801825835211973625643008),
      (1036493073827206309768085872405 / 20282409603651670423947251286016)⟩
    ⟨43,
      (6073793232274539847221946966595 / 20282409603651670423947251286016),
      (3036896616137269923610973483299 / 10141204801825835211973625643008)⟩)
    (PolyBound.shift (lo 3 + rr 3 * (2 * 2 + 1) - off 3) (pieceP 3)) (1) εin εout
    (110934025 / 1073741824) 3 = true := by
  decide +kernel

theorem p3_3 : lgammaRelOk (cfgJ 3) (sub 3 3 16
    ⟨4,
      (534760551189853102083407918625 / 10141204801825835211973625643008),
      (1069521102379706204166815837253 / 20282409603651670423947251286016)⟩
    ⟨43,
      (4051162190493165234400898509601 / 10141204801825835211973625643008),
      (8102324380986330468801797019205 / 20282409603651670423947251286016)⟩)
    (PolyBound.shift (lo 3 + rr 3 * (2 * 3 + 1) - off 3) (pieceP 3)) (1) εin εout
    (21741439 / 268435456) 5 = true := by
  decide +kernel

/-- Piece 3: `|lgamma x - P (x - off)| ≤ 2 ^ -63 |lgamma x|` on `[border 3, border 4]` widened
by `2 ^ -50` at each end. -/
theorem piece3 : ∀ x : ℝ, (border 3 : ℝ) - 1 / 2 ^ 50 ≤ x →
    x ≤ (border (3 + 1) : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - eval (pieceP 3) (x - off 3)| ≤ εout * |lgamma x| := by
  refine piece_of_subs 3 (by decide +kernel) fun k hk t ht => ?_
  interval_cases k
  · convert sub_bound 3 0 16 _ _ _ _ _ p3_0 t ht using 3 <;> norm_num
  · convert sub_bound 3 1 16 _ _ _ _ _ p3_1 t ht using 3 <;> norm_num
  · convert sub_bound 3 2 16 _ _ _ _ _ p3_2 t ht using 3 <;> norm_num
  · convert sub_bound 3 3 16 _ _ _ _ _ p3_3 t ht using 3 <;> norm_num

#print axioms piece0
#print axioms piece1
#print axioms piece2
#print axioms piece3

end Library.Numerics.Float64.Lgamma.LgammaPiecesA
