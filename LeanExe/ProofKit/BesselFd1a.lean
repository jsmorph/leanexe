import LeanExe.ProofKit.BesselSeg1

/-!
fdlibm's rational approximations `pone` and `qone` of `P1` and `Q1` from `e_j1.c` (FreeBSD msun
at commit `20381bce4b63975494a2f4bc84257f6932e6d379`) on the ranges that start at
`2`, `b3`, `b5`, where `b3 = 0x4006DB6D00000000` (about 2.8571) and
`b5 = 0x40122E8B00000000` (about 4.5454) are the boundaries that `e_j1.c` tests on the high word.
`pFd R S x` and `qFd (3/8) R S x` are fdlibm's formulas without rounding, with the coefficient lists
`ratOfWord` of the words that `e_j1.c` gives beside the decimal values.  Each theorem bounds
`|P1 x - pFd R S x|` or `|Q1 x - qFd (3/8) R S x|` for every real `x` in the range, from one
kernel check (`ratioCheckI`) per segment of `BesselSeg1` and, from 30 on, per Hankel's expansion.
-/

namespace LeanExe.ProofKit.BesselFd1a

open Set PolyBound PolyCalc BesselPQ BesselChain BesselRatio BesselLarge1 BesselSeg1

/-- The boundary `0x4006DB6D00000000` of fdlibm's ranges. -/
def b3 : ℚ := ratOfWord 0x4006DB6D00000000

/-- The boundary `0x40122E8B00000000` of fdlibm's ranges. -/
def b5 : ℚ := ratOfWord 0x40122E8B00000000

/-- `pr2` of `e_j1.c`. -/
def pr2 : List ℚ := [ratOfWord 0x3E7CE9D4F65544F4, ratOfWord 0x3FBDFF42BE760D83, ratOfWord 0x4002F2B7F98FAEC0, ratOfWord 0x40287C377F71A964, ratOfWord 0x4031B1A8177F8EE2, ratOfWord 0x40144B49A574C1FE]
/-- `ps2` of `e_j1.c`. -/
def ps2 : List ℚ := [ratOfWord 0x40356FBD8AD5ECDC, ratOfWord 0x405F529314F92CD5, ratOfWord 0x406D08D8D5A2DBD9, ratOfWord 0x405D6B7ADA1884A9, ratOfWord 0x4020BAB1F44E5192]

/-- `qr2` of `e_j1.c`. -/
def qr2 : List ℚ := [ratOfWord 0xBE87F12644C626D2, ratOfWord 0xBFBA3E8E9148B010, ratOfWord 0xC006048469BB4EDA, ratOfWord 0xC033A9E2C168907F, ratOfWord 0xC04529A3DE104AAA, ratOfWord 0xC0355F3639CF6E52]
/-- `qs2` of `e_j1.c`. -/
def qs2 : List ℚ := [ratOfWord 0x403D888A78AE64FF, ratOfWord 0x406F9F68DB821CBA, ratOfWord 0x4087AC05CE49A0F7, ratOfWord 0x40871B2548D4C029, ratOfWord 0x40637E5E3C3ED8D4, ratOfWord 0xC013D686E71BE86B]

/-- `pr3` of `e_j1.c`. -/
def pr3 : List ℚ := [ratOfWord 0x3E29FC21A7AD9EDD, ratOfWord 0x3FBDFFF55B21D17B, ratOfWord 0x400F76BCE85EAD8A, ratOfWord 0x40418F489DA6D129, ratOfWord 0x4056C3854D2C1837, ratOfWord 0x4048478F8EA83EE5]
/-- `ps3` of `e_j1.c`. -/
def ps3 : List ℚ := [ratOfWord 0x40416549A134069C, ratOfWord 0x40750C3307F1A75F, ratOfWord 0x40905B7C5037D523, ratOfWord 0x408BD67DA32E31E9, ratOfWord 0x4059F26D7C2EED53]

/-- `qr3` of `e_j1.c`. -/
def qr3 : List ℚ := [ratOfWord 0xBE35CFA9D38FC84F, ratOfWord 0xBFBA3FEB51AEED54, ratOfWord 0xC01270C23302D9FF, ratOfWord 0xC04CEC71C25D16DA, ratOfWord 0xC06C87D34718D55F, ratOfWord 0xC06B66B95F5C1BF6]
/-- `qs3` of `e_j1.c`. -/
def qs3 : List ℚ := [ratOfWord 0x4047D523CCD367E4, ratOfWord 0x40850EEBC031EE3E, ratOfWord 0x40AA684E448E7C9A, ratOfWord 0x40B5ABBAA61D54A6, ratOfWord 0x409DBC7A0DD4DF4B, ratOfWord 0xC060E670290A311F]

/-- `pr5` of `e_j1.c`. -/
def pr5 : List ℚ := [ratOfWord 0x3DAD0667DAE1CA7D, ratOfWord 0x3FBDFFFFE2C10043, ratOfWord 0x401B36046E6315E3, ratOfWord 0x405B13B9452602ED, ratOfWord 0x40802D16D052D649, ratOfWord 0x408085B8BB7E0CB7]
/-- `ps5` of `e_j1.c`. -/
def ps5 : List ℚ := [ratOfWord 0x404DA3EAA8AF633D, ratOfWord 0x408EFB361B066701, ratOfWord 0x40B4E9445706B6FB, ratOfWord 0x40BEA4B0B8A5BB15, ratOfWord 0x40978030036F5E51]

/-- `qr5` of `e_j1.c`. -/
def qr5 : List ℚ := [ratOfWord 0xBDB6FA431AA1A098, ratOfWord 0xBFBA3FFFCB597FEF, ratOfWord 0xC0201CE6CA03AD4B, ratOfWord 0xC066F56D6CA7B9B0, ratOfWord 0xC09574C66931734F, ratOfWord 0xC0A468E388FDA79D]
/-- `qs5` of `e_j1.c`. -/
def qs5 : List ℚ := [ratOfWord 0x405451B2FF5A11B2, ratOfWord 0x409F1F31E77BF839, ratOfWord 0x40D10F1F0D64CE29, ratOfWord 0x40E8576DAABAD197, ratOfWord 0x40DB4B04CF7C364B, ratOfWord 0xC0B26F2EFCFFA004]

theorem check_p2_0 :
    ratioCheckI (toInt 150 (pE seg1_0_0 pr2 ps2)) (toInt 70 (sTilde seg1_0_0.c ps2)) 150 70 68 1472 (-1) (1) 3 12 = true ∧
      isScaled 150 (pE seg1_0_0 pr2 ps2) = true ∧ isScaled 70 (sTilde seg1_0_0.c ps2) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 3 = 2 - seg1_0_0.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 3 = 9 / 2 ^ 2 - seg1_0_0.c ∧
      0 < (2 : ℚ) ∧ seg1_0_0.a ≤ 2 ∧ 9 / 2 ^ 2 ≤ seg1_0_0.b := by
  decide +kernel

theorem check_p2_1 :
    ratioCheckI (toInt 150 (pE seg1_0_1 pr2 ps2)) (toInt 70 (sTilde seg1_0_1.c ps2)) 150 70 68 1472 (-1) (1) 3 12 = true ∧
      isScaled 150 (pE seg1_0_1 pr2 ps2) = true ∧ isScaled 70 (sTilde seg1_0_1.c ps2) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 3 = 9 / 2 ^ 2 - seg1_0_1.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 3 = 5 / 2 ^ 1 - seg1_0_1.c ∧
      0 < (9 / 2 ^ 2 : ℚ) ∧ seg1_0_1.a ≤ 9 / 2 ^ 2 ∧ 5 / 2 ^ 1 ≤ seg1_0_1.b := by
  decide +kernel

theorem check_p2_2 :
    ratioCheckI (toInt 150 (pE seg1_0_2 pr2 ps2)) (toInt 70 (sTilde seg1_0_2.c ps2)) 150 70 68 1472 (-1) (1) 3 12 = true ∧
      isScaled 150 (pE seg1_0_2 pr2 ps2) = true ∧ isScaled 70 (sTilde seg1_0_2.c ps2) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 3 = 5 / 2 ^ 1 - seg1_0_2.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 3 = 11 / 2 ^ 2 - seg1_0_2.c ∧
      0 < (5 / 2 ^ 1 : ℚ) ∧ seg1_0_2.a ≤ 5 / 2 ^ 1 ∧ 11 / 2 ^ 2 ≤ seg1_0_2.b := by
  decide +kernel

theorem check_p2_3 :
    ratioCheckI (toInt 150 (pE seg1_0_3 pr2 ps2)) (toInt 70 (sTilde seg1_0_3.c ps2)) 150 70 68 1472 (-65536) (-9363) 19 12 = true ∧
      isScaled 150 (pE seg1_0_3 pr2 ps2) = true ∧ isScaled 70 (sTilde seg1_0_3.c ps2) = true ∧
      ((-65536 : ℤ) : ℚ) / 2 ^ 19 = 11 / 2 ^ 2 - seg1_0_3.c ∧ ((-9363 : ℤ) : ℚ) / 2 ^ 19 = b3 - seg1_0_3.c ∧
      0 < (11 / 2 ^ 2 : ℚ) ∧ seg1_0_3.a ≤ 11 / 2 ^ 2 ∧ b3 ≤ seg1_0_3.b := by
  decide +kernel

/-- `pone` on `[2, b3]`: within `1472/2^68 + 2^-70`, about `2 ^ -57.48`. -/
theorem pone_2 (x : ℝ) (hlo : (((2 : ℚ)) : ℝ) ≤ x) (hhi : x ≤ (((b3 : ℚ)) : ℝ)) :
    |P1 x - pFd pr2 ps2 x| ≤ 1472 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : pr2.length ≤ ps2.length + 1 := by decide
  rcases le_total x (((9 / 2 ^ 2 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast p_step (piece1_0, seg1_0_0) (segs_0_ok.1) (by simp [pieces, last]) pr2 ps2 hR (2) (9 / 2 ^ 2) 150 70 1472 _ _ _ ⟨check_p2_0.2.1, check_p2_0.2.2.1⟩ check_p2_0.1 ⟨check_p2_0.2.2.2.1, check_p2_0.2.2.2.2.1⟩ check_p2_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((5 / 2 ^ 1 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast p_step (piece1_0, seg1_0_1) (segs_0_ok.2.1) (by simp [pieces, last]) pr2 ps2 hR (9 / 2 ^ 2) (5 / 2 ^ 1) 150 70 1472 _ _ _ ⟨check_p2_1.2.1, check_p2_1.2.2.1⟩ check_p2_1.1 ⟨check_p2_1.2.2.2.1, check_p2_1.2.2.2.2.1⟩ check_p2_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((11 / 2 ^ 2 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast p_step (piece1_0, seg1_0_2) (segs_0_ok.2.2.1) (by simp [pieces, last]) pr2 ps2 hR (5 / 2 ^ 1) (11 / 2 ^ 2) 150 70 1472 _ _ _ ⟨check_p2_2.2.1, check_p2_2.2.2.1⟩ check_p2_2.1 ⟨check_p2_2.2.2.2.1, check_p2_2.2.2.2.2.1⟩ check_p2_2.2.2.2.2.2 x ⟨h1, h2⟩
  exact_mod_cast p_step (piece1_0, seg1_0_3) (segs_0_ok.2.2.2) (by simp [pieces, last]) pr2 ps2 hR (11 / 2 ^ 2) (b3) 150 70 1472 _ _ _ ⟨check_p2_3.2.1, check_p2_3.2.2.1⟩ check_p2_3.1 ⟨check_p2_3.2.2.2.1, check_p2_3.2.2.2.2.1⟩ check_p2_3.2.2.2.2.2 x ⟨h2, hhi⟩

theorem check_q2_0 :
    ratioCheckI (toInt 161 (qE (3 / 8) seg1_0_0 qr2 qs2)) (toInt 81 (qW seg1_0_0 qs2)) 161 81 68 171 (-1) (1) 3 12 = true ∧
      isScaled 161 (qE (3 / 8) seg1_0_0 qr2 qs2) = true ∧ isScaled 81 (qW seg1_0_0 qs2) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 3 = 2 - seg1_0_0.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 3 = 9 / 2 ^ 2 - seg1_0_0.c ∧
      0 < (2 : ℚ) ∧ seg1_0_0.a ≤ 2 ∧ 9 / 2 ^ 2 ≤ seg1_0_0.b := by
  decide +kernel

theorem check_q2_1 :
    ratioCheckI (toInt 161 (qE (3 / 8) seg1_0_1 qr2 qs2)) (toInt 81 (qW seg1_0_1 qs2)) 161 81 68 171 (-1) (1) 3 12 = true ∧
      isScaled 161 (qE (3 / 8) seg1_0_1 qr2 qs2) = true ∧ isScaled 81 (qW seg1_0_1 qs2) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 3 = 9 / 2 ^ 2 - seg1_0_1.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 3 = 5 / 2 ^ 1 - seg1_0_1.c ∧
      0 < (9 / 2 ^ 2 : ℚ) ∧ seg1_0_1.a ≤ 9 / 2 ^ 2 ∧ 5 / 2 ^ 1 ≤ seg1_0_1.b := by
  decide +kernel

theorem check_q2_2 :
    ratioCheckI (toInt 161 (qE (3 / 8) seg1_0_2 qr2 qs2)) (toInt 81 (qW seg1_0_2 qs2)) 161 81 68 171 (-1) (1) 3 12 = true ∧
      isScaled 161 (qE (3 / 8) seg1_0_2 qr2 qs2) = true ∧ isScaled 81 (qW seg1_0_2 qs2) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 3 = 5 / 2 ^ 1 - seg1_0_2.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 3 = 11 / 2 ^ 2 - seg1_0_2.c ∧
      0 < (5 / 2 ^ 1 : ℚ) ∧ seg1_0_2.a ≤ 5 / 2 ^ 1 ∧ 11 / 2 ^ 2 ≤ seg1_0_2.b := by
  decide +kernel

theorem check_q2_3 :
    ratioCheckI (toInt 161 (qE (3 / 8) seg1_0_3 qr2 qs2)) (toInt 81 (qW seg1_0_3 qs2)) 161 81 68 171 (-65536) (-9363) 19 12 = true ∧
      isScaled 161 (qE (3 / 8) seg1_0_3 qr2 qs2) = true ∧ isScaled 81 (qW seg1_0_3 qs2) = true ∧
      ((-65536 : ℤ) : ℚ) / 2 ^ 19 = 11 / 2 ^ 2 - seg1_0_3.c ∧ ((-9363 : ℤ) : ℚ) / 2 ^ 19 = b3 - seg1_0_3.c ∧
      0 < (11 / 2 ^ 2 : ℚ) ∧ seg1_0_3.a ≤ 11 / 2 ^ 2 ∧ b3 ≤ seg1_0_3.b := by
  decide +kernel

/-- `qone` on `[2, b3]`: within `171/2^68 + 2^-70`, about `2 ^ -60.58`. -/
theorem qone_2 (x : ℝ) (hlo : (((2 : ℚ)) : ℝ) ≤ x) (hhi : x ≤ (((b3 : ℚ)) : ℝ)) :
    |Q1 x - qFd (3 / 8) qr2 qs2 x| ≤ 171 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : qr2.length ≤ qs2.length + 1 := by decide
  rcases le_total x (((9 / 2 ^ 2 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast q_step (piece1_0, seg1_0_0) (segs_0_ok.1) (by simp [pieces, last]) qr2 qs2 hR (2) (9 / 2 ^ 2) 161 81 171 _ _ _ ⟨check_q2_0.2.1, check_q2_0.2.2.1⟩ check_q2_0.1 ⟨check_q2_0.2.2.2.1, check_q2_0.2.2.2.2.1⟩ check_q2_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((5 / 2 ^ 1 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast q_step (piece1_0, seg1_0_1) (segs_0_ok.2.1) (by simp [pieces, last]) qr2 qs2 hR (9 / 2 ^ 2) (5 / 2 ^ 1) 161 81 171 _ _ _ ⟨check_q2_1.2.1, check_q2_1.2.2.1⟩ check_q2_1.1 ⟨check_q2_1.2.2.2.1, check_q2_1.2.2.2.2.1⟩ check_q2_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((11 / 2 ^ 2 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast q_step (piece1_0, seg1_0_2) (segs_0_ok.2.2.1) (by simp [pieces, last]) qr2 qs2 hR (5 / 2 ^ 1) (11 / 2 ^ 2) 161 81 171 _ _ _ ⟨check_q2_2.2.1, check_q2_2.2.2.1⟩ check_q2_2.1 ⟨check_q2_2.2.2.2.1, check_q2_2.2.2.2.2.1⟩ check_q2_2.2.2.2.2.2 x ⟨h1, h2⟩
  exact_mod_cast q_step (piece1_0, seg1_0_3) (segs_0_ok.2.2.2) (by simp [pieces, last]) qr2 qs2 hR (11 / 2 ^ 2) (b3) 161 81 171 _ _ _ ⟨check_q2_3.2.1, check_q2_3.2.2.1⟩ check_q2_3.1 ⟨check_q2_3.2.2.2.1, check_q2_3.2.2.2.2.1⟩ check_q2_3.2.2.2.2.2 x ⟨h2, hhi⟩

theorem check_p3_0 :
    ratioCheckI (toInt 149 (pE seg1_0_3 pr3 ps3)) (toInt 69 (sTilde seg1_0_3.c ps3)) 149 69 68 2231 (-9363) (65536) 19 12 = true ∧
      isScaled 149 (pE seg1_0_3 pr3 ps3) = true ∧ isScaled 69 (sTilde seg1_0_3.c ps3) = true ∧
      ((-9363 : ℤ) : ℚ) / 2 ^ 19 = b3 - seg1_0_3.c ∧ ((65536 : ℤ) : ℚ) / 2 ^ 19 = 3 - seg1_0_3.c ∧
      0 < (b3 : ℚ) ∧ seg1_0_3.a ≤ b3 ∧ 3 ≤ seg1_0_3.b := by
  decide +kernel

theorem check_p3_1 :
    ratioCheckI (toInt 157 (pE seg1_1_0 pr3 ps3)) (toInt 77 (sTilde seg1_1_0.c ps3)) 157 77 68 2231 (-3) (3) 4 12 = true ∧
      isScaled 157 (pE seg1_1_0 pr3 ps3) = true ∧ isScaled 77 (sTilde seg1_1_0.c ps3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 3 - seg1_1_0.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 27 / 2 ^ 3 - seg1_1_0.c ∧
      0 < (3 : ℚ) ∧ seg1_1_0.a ≤ 3 ∧ 27 / 2 ^ 3 ≤ seg1_1_0.b := by
  decide +kernel

theorem check_p3_2 :
    ratioCheckI (toInt 157 (pE seg1_1_1 pr3 ps3)) (toInt 77 (sTilde seg1_1_1.c ps3)) 157 77 68 2231 (-3) (3) 4 12 = true ∧
      isScaled 157 (pE seg1_1_1 pr3 ps3) = true ∧ isScaled 77 (sTilde seg1_1_1.c ps3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 27 / 2 ^ 3 - seg1_1_1.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 15 / 2 ^ 2 - seg1_1_1.c ∧
      0 < (27 / 2 ^ 3 : ℚ) ∧ seg1_1_1.a ≤ 27 / 2 ^ 3 ∧ 15 / 2 ^ 2 ≤ seg1_1_1.b := by
  decide +kernel

theorem check_p3_3 :
    ratioCheckI (toInt 157 (pE seg1_1_2 pr3 ps3)) (toInt 77 (sTilde seg1_1_2.c ps3)) 157 77 68 2231 (-3) (3) 4 12 = true ∧
      isScaled 157 (pE seg1_1_2 pr3 ps3) = true ∧ isScaled 77 (sTilde seg1_1_2.c ps3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 15 / 2 ^ 2 - seg1_1_2.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 33 / 2 ^ 3 - seg1_1_2.c ∧
      0 < (15 / 2 ^ 2 : ℚ) ∧ seg1_1_2.a ≤ 15 / 2 ^ 2 ∧ 33 / 2 ^ 3 ≤ seg1_1_2.b := by
  decide +kernel

theorem check_p3_4 :
    ratioCheckI (toInt 157 (pE seg1_1_3 pr3 ps3)) (toInt 77 (sTilde seg1_1_3.c ps3)) 157 77 68 2231 (-3) (3) 4 12 = true ∧
      isScaled 157 (pE seg1_1_3 pr3 ps3) = true ∧ isScaled 77 (sTilde seg1_1_3.c ps3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 33 / 2 ^ 3 - seg1_1_3.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 9 / 2 ^ 1 - seg1_1_3.c ∧
      0 < (33 / 2 ^ 3 : ℚ) ∧ seg1_1_3.a ≤ 33 / 2 ^ 3 ∧ 9 / 2 ^ 1 ≤ seg1_1_3.b := by
  decide +kernel

theorem check_p3_5 :
    ratioCheckI (toInt 157 (pE seg1_2_0 pr3 ps3)) (toInt 77 (sTilde seg1_2_0.c ps3)) 157 77 68 2231 (-81920) (-70005) 18 12 = true ∧
      isScaled 157 (pE seg1_2_0 pr3 ps3) = true ∧ isScaled 77 (sTilde seg1_2_0.c ps3) = true ∧
      ((-81920 : ℤ) : ℚ) / 2 ^ 18 = 9 / 2 ^ 1 - seg1_2_0.c ∧ ((-70005 : ℤ) : ℚ) / 2 ^ 18 = b5 - seg1_2_0.c ∧
      0 < (9 / 2 ^ 1 : ℚ) ∧ seg1_2_0.a ≤ 9 / 2 ^ 1 ∧ b5 ≤ seg1_2_0.b := by
  decide +kernel

/-- `pone` on `[b3, b5]`: within `2231/2^68 + 2^-70`, about `2 ^ -56.88`. -/
theorem pone_3 (x : ℝ) (hlo : (((b3 : ℚ)) : ℝ) ≤ x) (hhi : x ≤ (((b5 : ℚ)) : ℝ)) :
    |P1 x - pFd pr3 ps3 x| ≤ 2231 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : pr3.length ≤ ps3.length + 1 := by decide
  rcases le_total x (((3 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast p_step (piece1_0, seg1_0_3) (segs_0_ok.2.2.2) (by simp [pieces, last]) pr3 ps3 hR (b3) (3) 149 69 2231 _ _ _ ⟨check_p3_0.2.1, check_p3_0.2.2.1⟩ check_p3_0.1 ⟨check_p3_0.2.2.2.1, check_p3_0.2.2.2.2.1⟩ check_p3_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((27 / 2 ^ 3 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast p_step (piece1_1, seg1_1_0) (segs_1_ok.1) (by simp [pieces, last]) pr3 ps3 hR (3) (27 / 2 ^ 3) 157 77 2231 _ _ _ ⟨check_p3_1.2.1, check_p3_1.2.2.1⟩ check_p3_1.1 ⟨check_p3_1.2.2.2.1, check_p3_1.2.2.2.2.1⟩ check_p3_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((15 / 2 ^ 2 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast p_step (piece1_1, seg1_1_1) (segs_1_ok.2.1) (by simp [pieces, last]) pr3 ps3 hR (27 / 2 ^ 3) (15 / 2 ^ 2) 157 77 2231 _ _ _ ⟨check_p3_2.2.1, check_p3_2.2.2.1⟩ check_p3_2.1 ⟨check_p3_2.2.2.2.1, check_p3_2.2.2.2.2.1⟩ check_p3_2.2.2.2.2.2 x ⟨h1, h2⟩
  rcases le_total x (((33 / 2 ^ 3 : ℚ)) : ℝ) with h3 | h3
  · exact_mod_cast p_step (piece1_1, seg1_1_2) (segs_1_ok.2.2.1) (by simp [pieces, last]) pr3 ps3 hR (15 / 2 ^ 2) (33 / 2 ^ 3) 157 77 2231 _ _ _ ⟨check_p3_3.2.1, check_p3_3.2.2.1⟩ check_p3_3.1 ⟨check_p3_3.2.2.2.1, check_p3_3.2.2.2.2.1⟩ check_p3_3.2.2.2.2.2 x ⟨h2, h3⟩
  rcases le_total x (((9 / 2 ^ 1 : ℚ)) : ℝ) with h4 | h4
  · exact_mod_cast p_step (piece1_1, seg1_1_3) (segs_1_ok.2.2.2) (by simp [pieces, last]) pr3 ps3 hR (33 / 2 ^ 3) (9 / 2 ^ 1) 157 77 2231 _ _ _ ⟨check_p3_4.2.1, check_p3_4.2.2.1⟩ check_p3_4.1 ⟨check_p3_4.2.2.2.1, check_p3_4.2.2.2.2.1⟩ check_p3_4.2.2.2.2.2 x ⟨h3, h4⟩
  exact_mod_cast p_step (piece1_2, seg1_2_0) (segs_2_ok.1) (by simp [pieces, last]) pr3 ps3 hR (9 / 2 ^ 1) (b5) 157 77 2231 _ _ _ ⟨check_p3_5.2.1, check_p3_5.2.2.1⟩ check_p3_5.1 ⟨check_p3_5.2.2.2.1, check_p3_5.2.2.2.2.1⟩ check_p3_5.2.2.2.2.2 x ⟨h4, hhi⟩

theorem check_q3_0 :
    ratioCheckI (toInt 158 (qE (3 / 8) seg1_0_3 qr3 qs3)) (toInt 78 (qW seg1_0_3 qs3)) 158 78 68 127 (-9363) (65536) 19 12 = true ∧
      isScaled 158 (qE (3 / 8) seg1_0_3 qr3 qs3) = true ∧ isScaled 78 (qW seg1_0_3 qs3) = true ∧
      ((-9363 : ℤ) : ℚ) / 2 ^ 19 = b3 - seg1_0_3.c ∧ ((65536 : ℤ) : ℚ) / 2 ^ 19 = 3 - seg1_0_3.c ∧
      0 < (b3 : ℚ) ∧ seg1_0_3.a ≤ b3 ∧ 3 ≤ seg1_0_3.b := by
  decide +kernel

theorem check_q3_1 :
    ratioCheckI (toInt 169 (qE (3 / 8) seg1_1_0 qr3 qs3)) (toInt 89 (qW seg1_1_0 qs3)) 169 89 68 127 (-3) (3) 4 12 = true ∧
      isScaled 169 (qE (3 / 8) seg1_1_0 qr3 qs3) = true ∧ isScaled 89 (qW seg1_1_0 qs3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 3 - seg1_1_0.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 27 / 2 ^ 3 - seg1_1_0.c ∧
      0 < (3 : ℚ) ∧ seg1_1_0.a ≤ 3 ∧ 27 / 2 ^ 3 ≤ seg1_1_0.b := by
  decide +kernel

theorem check_q3_2 :
    ratioCheckI (toInt 169 (qE (3 / 8) seg1_1_1 qr3 qs3)) (toInt 89 (qW seg1_1_1 qs3)) 169 89 68 127 (-3) (3) 4 12 = true ∧
      isScaled 169 (qE (3 / 8) seg1_1_1 qr3 qs3) = true ∧ isScaled 89 (qW seg1_1_1 qs3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 27 / 2 ^ 3 - seg1_1_1.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 15 / 2 ^ 2 - seg1_1_1.c ∧
      0 < (27 / 2 ^ 3 : ℚ) ∧ seg1_1_1.a ≤ 27 / 2 ^ 3 ∧ 15 / 2 ^ 2 ≤ seg1_1_1.b := by
  decide +kernel

theorem check_q3_3 :
    ratioCheckI (toInt 169 (qE (3 / 8) seg1_1_2 qr3 qs3)) (toInt 89 (qW seg1_1_2 qs3)) 169 89 68 127 (-3) (3) 4 12 = true ∧
      isScaled 169 (qE (3 / 8) seg1_1_2 qr3 qs3) = true ∧ isScaled 89 (qW seg1_1_2 qs3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 15 / 2 ^ 2 - seg1_1_2.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 33 / 2 ^ 3 - seg1_1_2.c ∧
      0 < (15 / 2 ^ 2 : ℚ) ∧ seg1_1_2.a ≤ 15 / 2 ^ 2 ∧ 33 / 2 ^ 3 ≤ seg1_1_2.b := by
  decide +kernel

theorem check_q3_4 :
    ratioCheckI (toInt 169 (qE (3 / 8) seg1_1_3 qr3 qs3)) (toInt 89 (qW seg1_1_3 qs3)) 169 89 68 127 (-3) (3) 4 12 = true ∧
      isScaled 169 (qE (3 / 8) seg1_1_3 qr3 qs3) = true ∧ isScaled 89 (qW seg1_1_3 qs3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 33 / 2 ^ 3 - seg1_1_3.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 9 / 2 ^ 1 - seg1_1_3.c ∧
      0 < (33 / 2 ^ 3 : ℚ) ∧ seg1_1_3.a ≤ 33 / 2 ^ 3 ∧ 9 / 2 ^ 1 ≤ seg1_1_3.b := by
  decide +kernel

theorem check_q3_5 :
    ratioCheckI (toInt 169 (qE (3 / 8) seg1_2_0 qr3 qs3)) (toInt 89 (qW seg1_2_0 qs3)) 169 89 68 127 (-81920) (-70005) 18 12 = true ∧
      isScaled 169 (qE (3 / 8) seg1_2_0 qr3 qs3) = true ∧ isScaled 89 (qW seg1_2_0 qs3) = true ∧
      ((-81920 : ℤ) : ℚ) / 2 ^ 18 = 9 / 2 ^ 1 - seg1_2_0.c ∧ ((-70005 : ℤ) : ℚ) / 2 ^ 18 = b5 - seg1_2_0.c ∧
      0 < (9 / 2 ^ 1 : ℚ) ∧ seg1_2_0.a ≤ 9 / 2 ^ 1 ∧ b5 ≤ seg1_2_0.b := by
  decide +kernel

/-- `qone` on `[b3, b5]`: within `127/2^68 + 2^-70`, about `2 ^ -61.01`. -/
theorem qone_3 (x : ℝ) (hlo : (((b3 : ℚ)) : ℝ) ≤ x) (hhi : x ≤ (((b5 : ℚ)) : ℝ)) :
    |Q1 x - qFd (3 / 8) qr3 qs3 x| ≤ 127 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : qr3.length ≤ qs3.length + 1 := by decide
  rcases le_total x (((3 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast q_step (piece1_0, seg1_0_3) (segs_0_ok.2.2.2) (by simp [pieces, last]) qr3 qs3 hR (b3) (3) 158 78 127 _ _ _ ⟨check_q3_0.2.1, check_q3_0.2.2.1⟩ check_q3_0.1 ⟨check_q3_0.2.2.2.1, check_q3_0.2.2.2.2.1⟩ check_q3_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((27 / 2 ^ 3 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast q_step (piece1_1, seg1_1_0) (segs_1_ok.1) (by simp [pieces, last]) qr3 qs3 hR (3) (27 / 2 ^ 3) 169 89 127 _ _ _ ⟨check_q3_1.2.1, check_q3_1.2.2.1⟩ check_q3_1.1 ⟨check_q3_1.2.2.2.1, check_q3_1.2.2.2.2.1⟩ check_q3_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((15 / 2 ^ 2 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast q_step (piece1_1, seg1_1_1) (segs_1_ok.2.1) (by simp [pieces, last]) qr3 qs3 hR (27 / 2 ^ 3) (15 / 2 ^ 2) 169 89 127 _ _ _ ⟨check_q3_2.2.1, check_q3_2.2.2.1⟩ check_q3_2.1 ⟨check_q3_2.2.2.2.1, check_q3_2.2.2.2.2.1⟩ check_q3_2.2.2.2.2.2 x ⟨h1, h2⟩
  rcases le_total x (((33 / 2 ^ 3 : ℚ)) : ℝ) with h3 | h3
  · exact_mod_cast q_step (piece1_1, seg1_1_2) (segs_1_ok.2.2.1) (by simp [pieces, last]) qr3 qs3 hR (15 / 2 ^ 2) (33 / 2 ^ 3) 169 89 127 _ _ _ ⟨check_q3_3.2.1, check_q3_3.2.2.1⟩ check_q3_3.1 ⟨check_q3_3.2.2.2.1, check_q3_3.2.2.2.2.1⟩ check_q3_3.2.2.2.2.2 x ⟨h2, h3⟩
  rcases le_total x (((9 / 2 ^ 1 : ℚ)) : ℝ) with h4 | h4
  · exact_mod_cast q_step (piece1_1, seg1_1_3) (segs_1_ok.2.2.2) (by simp [pieces, last]) qr3 qs3 hR (33 / 2 ^ 3) (9 / 2 ^ 1) 169 89 127 _ _ _ ⟨check_q3_4.2.1, check_q3_4.2.2.1⟩ check_q3_4.1 ⟨check_q3_4.2.2.2.1, check_q3_4.2.2.2.2.1⟩ check_q3_4.2.2.2.2.2 x ⟨h3, h4⟩
  exact_mod_cast q_step (piece1_2, seg1_2_0) (segs_2_ok.1) (by simp [pieces, last]) qr3 qs3 hR (9 / 2 ^ 1) (b5) 169 89 127 _ _ _ ⟨check_q3_5.2.1, check_q3_5.2.2.1⟩ check_q3_5.1 ⟨check_q3_5.2.2.2.1, check_q3_5.2.2.2.2.1⟩ check_q3_5.2.2.2.2.2 x ⟨h4, hhi⟩

theorem check_p5_0 :
    ratioCheckI (toInt 159 (pE seg1_2_0 pr5 ps5)) (toInt 79 (sTilde seg1_2_0.c ps5)) 159 79 68 321 (-70005) (81920) 18 12 = true ∧
      isScaled 159 (pE seg1_2_0 pr5 ps5) = true ∧ isScaled 79 (sTilde seg1_2_0.c ps5) = true ∧
      ((-70005 : ℤ) : ℚ) / 2 ^ 18 = b5 - seg1_2_0.c ∧ ((81920 : ℤ) : ℚ) / 2 ^ 18 = 41 / 2 ^ 3 - seg1_2_0.c ∧
      0 < (b5 : ℚ) ∧ seg1_2_0.a ≤ b5 ∧ 41 / 2 ^ 3 ≤ seg1_2_0.b := by
  decide +kernel

theorem check_p5_1 :
    ratioCheckI (toInt 159 (pE seg1_2_1 pr5 ps5)) (toInt 79 (sTilde seg1_2_1.c ps5)) 159 79 68 321 (-5) (5) 4 12 = true ∧
      isScaled 159 (pE seg1_2_1 pr5 ps5) = true ∧ isScaled 79 (sTilde seg1_2_1.c ps5) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 4 = 41 / 2 ^ 3 - seg1_2_1.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 4 = 23 / 2 ^ 2 - seg1_2_1.c ∧
      0 < (41 / 2 ^ 3 : ℚ) ∧ seg1_2_1.a ≤ 41 / 2 ^ 3 ∧ 23 / 2 ^ 2 ≤ seg1_2_1.b := by
  decide +kernel

theorem check_p5_2 :
    ratioCheckI (toInt 159 (pE seg1_2_2 pr5 ps5)) (toInt 79 (sTilde seg1_2_2.c ps5)) 159 79 68 321 (-5) (5) 4 12 = true ∧
      isScaled 159 (pE seg1_2_2 pr5 ps5) = true ∧ isScaled 79 (sTilde seg1_2_2.c ps5) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 4 = 23 / 2 ^ 2 - seg1_2_2.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 4 = 51 / 2 ^ 3 - seg1_2_2.c ∧
      0 < (23 / 2 ^ 2 : ℚ) ∧ seg1_2_2.a ≤ 23 / 2 ^ 2 ∧ 51 / 2 ^ 3 ≤ seg1_2_2.b := by
  decide +kernel

theorem check_p5_3 :
    ratioCheckI (toInt 159 (pE seg1_2_3 pr5 ps5)) (toInt 79 (sTilde seg1_2_3.c ps5)) 159 79 68 321 (-5) (5) 4 12 = true ∧
      isScaled 159 (pE seg1_2_3 pr5 ps5) = true ∧ isScaled 79 (sTilde seg1_2_3.c ps5) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 4 = 51 / 2 ^ 3 - seg1_2_3.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 4 = 7 - seg1_2_3.c ∧
      0 < (51 / 2 ^ 3 : ℚ) ∧ seg1_2_3.a ≤ 51 / 2 ^ 3 ∧ 7 ≤ seg1_2_3.b := by
  decide +kernel

theorem check_p5_4 :
    ratioCheckI (toInt 135 (pE seg1_3_0 pr5 ps5)) (toInt 55 (sTilde seg1_3_0.c ps5)) 135 55 68 321 (-1) (1) 1 12 = true ∧
      isScaled 135 (pE seg1_3_0 pr5 ps5) = true ∧ isScaled 55 (sTilde seg1_3_0.c ps5) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 1 = 7 - seg1_3_0.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 1 = 8 - seg1_3_0.c ∧
      0 < (7 : ℚ) ∧ seg1_3_0.a ≤ 7 ∧ 8 ≤ seg1_3_0.b := by
  decide +kernel

/-- `pone` on `[b5, 8]`: within `321/2^68 + 2^-70`, about `2 ^ -59.67`. -/
theorem pone_5 (x : ℝ) (hlo : (((b5 : ℚ)) : ℝ) ≤ x) (hhi : x ≤ (((8 : ℚ)) : ℝ)) :
    |P1 x - pFd pr5 ps5 x| ≤ 321 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : pr5.length ≤ ps5.length + 1 := by decide
  rcases le_total x (((41 / 2 ^ 3 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast p_step (piece1_2, seg1_2_0) (segs_2_ok.1) (by simp [pieces, last]) pr5 ps5 hR (b5) (41 / 2 ^ 3) 159 79 321 _ _ _ ⟨check_p5_0.2.1, check_p5_0.2.2.1⟩ check_p5_0.1 ⟨check_p5_0.2.2.2.1, check_p5_0.2.2.2.2.1⟩ check_p5_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((23 / 2 ^ 2 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast p_step (piece1_2, seg1_2_1) (segs_2_ok.2.1) (by simp [pieces, last]) pr5 ps5 hR (41 / 2 ^ 3) (23 / 2 ^ 2) 159 79 321 _ _ _ ⟨check_p5_1.2.1, check_p5_1.2.2.1⟩ check_p5_1.1 ⟨check_p5_1.2.2.2.1, check_p5_1.2.2.2.2.1⟩ check_p5_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((51 / 2 ^ 3 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast p_step (piece1_2, seg1_2_2) (segs_2_ok.2.2.1) (by simp [pieces, last]) pr5 ps5 hR (23 / 2 ^ 2) (51 / 2 ^ 3) 159 79 321 _ _ _ ⟨check_p5_2.2.1, check_p5_2.2.2.1⟩ check_p5_2.1 ⟨check_p5_2.2.2.2.1, check_p5_2.2.2.2.2.1⟩ check_p5_2.2.2.2.2.2 x ⟨h1, h2⟩
  rcases le_total x (((7 : ℚ)) : ℝ) with h3 | h3
  · exact_mod_cast p_step (piece1_2, seg1_2_3) (segs_2_ok.2.2.2) (by simp [pieces, last]) pr5 ps5 hR (51 / 2 ^ 3) (7) 159 79 321 _ _ _ ⟨check_p5_3.2.1, check_p5_3.2.2.1⟩ check_p5_3.1 ⟨check_p5_3.2.2.2.1, check_p5_3.2.2.2.2.1⟩ check_p5_3.2.2.2.2.2 x ⟨h2, h3⟩
  exact_mod_cast p_step (piece1_3, seg1_3_0) (segs_3_ok.1) (by simp [pieces, last]) pr5 ps5 hR (7) (8) 135 55 321 _ _ _ ⟨check_p5_4.2.1, check_p5_4.2.2.1⟩ check_p5_4.1 ⟨check_p5_4.2.2.2.1, check_p5_4.2.2.2.2.1⟩ check_p5_4.2.2.2.2.2 x ⟨h3, hhi⟩

theorem check_q5_0 :
    ratioCheckI (toInt 169 (qE (3 / 8) seg1_2_0 qr5 qs5)) (toInt 89 (qW seg1_2_0 qs5)) 169 89 68 29 (-70005) (81920) 18 12 = true ∧
      isScaled 169 (qE (3 / 8) seg1_2_0 qr5 qs5) = true ∧ isScaled 89 (qW seg1_2_0 qs5) = true ∧
      ((-70005 : ℤ) : ℚ) / 2 ^ 18 = b5 - seg1_2_0.c ∧ ((81920 : ℤ) : ℚ) / 2 ^ 18 = 41 / 2 ^ 3 - seg1_2_0.c ∧
      0 < (b5 : ℚ) ∧ seg1_2_0.a ≤ b5 ∧ 41 / 2 ^ 3 ≤ seg1_2_0.b := by
  decide +kernel

theorem check_q5_1 :
    ratioCheckI (toInt 169 (qE (3 / 8) seg1_2_1 qr5 qs5)) (toInt 89 (qW seg1_2_1 qs5)) 169 89 68 29 (-5) (5) 4 12 = true ∧
      isScaled 169 (qE (3 / 8) seg1_2_1 qr5 qs5) = true ∧ isScaled 89 (qW seg1_2_1 qs5) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 4 = 41 / 2 ^ 3 - seg1_2_1.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 4 = 23 / 2 ^ 2 - seg1_2_1.c ∧
      0 < (41 / 2 ^ 3 : ℚ) ∧ seg1_2_1.a ≤ 41 / 2 ^ 3 ∧ 23 / 2 ^ 2 ≤ seg1_2_1.b := by
  decide +kernel

theorem check_q5_2 :
    ratioCheckI (toInt 169 (qE (3 / 8) seg1_2_2 qr5 qs5)) (toInt 89 (qW seg1_2_2 qs5)) 169 89 68 29 (-5) (5) 4 12 = true ∧
      isScaled 169 (qE (3 / 8) seg1_2_2 qr5 qs5) = true ∧ isScaled 89 (qW seg1_2_2 qs5) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 4 = 23 / 2 ^ 2 - seg1_2_2.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 4 = 51 / 2 ^ 3 - seg1_2_2.c ∧
      0 < (23 / 2 ^ 2 : ℚ) ∧ seg1_2_2.a ≤ 23 / 2 ^ 2 ∧ 51 / 2 ^ 3 ≤ seg1_2_2.b := by
  decide +kernel

theorem check_q5_3 :
    ratioCheckI (toInt 169 (qE (3 / 8) seg1_2_3 qr5 qs5)) (toInt 89 (qW seg1_2_3 qs5)) 169 89 68 29 (-5) (5) 4 12 = true ∧
      isScaled 169 (qE (3 / 8) seg1_2_3 qr5 qs5) = true ∧ isScaled 89 (qW seg1_2_3 qs5) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 4 = 51 / 2 ^ 3 - seg1_2_3.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 4 = 7 - seg1_2_3.c ∧
      0 < (51 / 2 ^ 3 : ℚ) ∧ seg1_2_3.a ≤ 51 / 2 ^ 3 ∧ 7 ≤ seg1_2_3.b := by
  decide +kernel

theorem check_q5_4 :
    ratioCheckI (toInt 136 (qE (3 / 8) seg1_3_0 qr5 qs5)) (toInt 56 (qW seg1_3_0 qs5)) 136 56 68 29 (-1) (1) 1 12 = true ∧
      isScaled 136 (qE (3 / 8) seg1_3_0 qr5 qs5) = true ∧ isScaled 56 (qW seg1_3_0 qs5) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 1 = 7 - seg1_3_0.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 1 = 8 - seg1_3_0.c ∧
      0 < (7 : ℚ) ∧ seg1_3_0.a ≤ 7 ∧ 8 ≤ seg1_3_0.b := by
  decide +kernel

/-- `qone` on `[b5, 8]`: within `29/2^68 + 2^-70`, about `2 ^ -63.13`. -/
theorem qone_5 (x : ℝ) (hlo : (((b5 : ℚ)) : ℝ) ≤ x) (hhi : x ≤ (((8 : ℚ)) : ℝ)) :
    |Q1 x - qFd (3 / 8) qr5 qs5 x| ≤ 29 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : qr5.length ≤ qs5.length + 1 := by decide
  rcases le_total x (((41 / 2 ^ 3 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast q_step (piece1_2, seg1_2_0) (segs_2_ok.1) (by simp [pieces, last]) qr5 qs5 hR (b5) (41 / 2 ^ 3) 169 89 29 _ _ _ ⟨check_q5_0.2.1, check_q5_0.2.2.1⟩ check_q5_0.1 ⟨check_q5_0.2.2.2.1, check_q5_0.2.2.2.2.1⟩ check_q5_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((23 / 2 ^ 2 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast q_step (piece1_2, seg1_2_1) (segs_2_ok.2.1) (by simp [pieces, last]) qr5 qs5 hR (41 / 2 ^ 3) (23 / 2 ^ 2) 169 89 29 _ _ _ ⟨check_q5_1.2.1, check_q5_1.2.2.1⟩ check_q5_1.1 ⟨check_q5_1.2.2.2.1, check_q5_1.2.2.2.2.1⟩ check_q5_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((51 / 2 ^ 3 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast q_step (piece1_2, seg1_2_2) (segs_2_ok.2.2.1) (by simp [pieces, last]) qr5 qs5 hR (23 / 2 ^ 2) (51 / 2 ^ 3) 169 89 29 _ _ _ ⟨check_q5_2.2.1, check_q5_2.2.2.1⟩ check_q5_2.1 ⟨check_q5_2.2.2.2.1, check_q5_2.2.2.2.2.1⟩ check_q5_2.2.2.2.2.2 x ⟨h1, h2⟩
  rcases le_total x (((7 : ℚ)) : ℝ) with h3 | h3
  · exact_mod_cast q_step (piece1_2, seg1_2_3) (segs_2_ok.2.2.2) (by simp [pieces, last]) qr5 qs5 hR (51 / 2 ^ 3) (7) 169 89 29 _ _ _ ⟨check_q5_3.2.1, check_q5_3.2.2.1⟩ check_q5_3.1 ⟨check_q5_3.2.2.2.1, check_q5_3.2.2.2.2.1⟩ check_q5_3.2.2.2.2.2 x ⟨h2, h3⟩
  exact_mod_cast q_step (piece1_3, seg1_3_0) (segs_3_ok.1) (by simp [pieces, last]) qr5 qs5 hR (7) (8) 136 56 29 _ _ _ ⟨check_q5_4.2.1, check_q5_4.2.2.1⟩ check_q5_4.1 ⟨check_q5_4.2.2.2.1, check_q5_4.2.2.2.2.1⟩ check_q5_4.2.2.2.2.2 x ⟨h3, hhi⟩

#print axioms pone_2
#print axioms qone_2
#print axioms pone_3
#print axioms qone_3
#print axioms pone_5
#print axioms qone_5

end LeanExe.ProofKit.BesselFd1a
