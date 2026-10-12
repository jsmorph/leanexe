import LeanExe.ProofKit.BesselSeg1

/-!
fdlibm's rational approximations `pone` and `qone` of `P1` and `Q1` from `e_j1.c` (FreeBSD msun
at commit `20381bce4b63975494a2f4bc84257f6932e6d379`) on the ranges that start at
`8`, where `b3 = 0x4006DB6D00000000` (about 2.8571) and
`b5 = 0x40122E8B00000000` (about 4.5454) are the boundaries that `e_j1.c` tests on the high word.
`pFd R S x` and `qFd (3/8) R S x` are fdlibm's formulas without rounding, with the coefficient lists
`ratOfWord` of the words that `e_j1.c` gives beside the decimal values.  Each theorem bounds
`|P1 x - pFd R S x|` or `|Q1 x - qFd (3/8) R S x|` for every real `x` in the range, from one
kernel check (`ratioCheckI`) per segment of `BesselSeg1` and, from 30 on, per Hankel's expansion.
-/

namespace LeanExe.ProofKit.BesselFd1b

open Set PolyBound PolyCalc BesselPQ BesselChain BesselRatio BesselLarge1 BesselSeg1

/-- The boundary `0x4006DB6D00000000` of fdlibm's ranges. -/
def b3 : ℚ := ratOfWord 0x4006DB6D00000000

/-- The boundary `0x40122E8B00000000` of fdlibm's ranges. -/
def b5 : ℚ := ratOfWord 0x40122E8B00000000

/-- `pr8` of `e_j1.c`. -/
def pr8 : List ℚ := [ratOfWord 0x0000000000000000, ratOfWord 0x3FBDFFFFFFFFFCCE, ratOfWord 0x402A7A9D357F7FCE, ratOfWord 0x4079C0D4652EA590, ratOfWord 0x40AE457DA3A532CC, ratOfWord 0x40BEEA7AC32782DD]
/-- `ps8` of `e_j1.c`. -/
def ps8 : List ℚ := [ratOfWord 0x405C8D458E656CAC, ratOfWord 0x40AC85DC964D274F, ratOfWord 0x40E20B8697C5BB7F, ratOfWord 0x40F7D42CB28F17BB, ratOfWord 0x40DE1511697A0B2D]

/-- `qr8` of `e_j1.c`. -/
def qr8 : List ℚ := [ratOfWord 0x0000000000000000, ratOfWord 0xBFBA3FFFFFFFFDF3, ratOfWord 0xC0304591A26779F7, ratOfWord 0xC087BCD053E4B576, ratOfWord 0xC0C724E740F87415, ratOfWord 0xC0E7A6D065D09C6A]
/-- `qs8` of `e_j1.c`. -/
def qs8 : List ℚ := [ratOfWord 0x40642CA6DE5BCDE5, ratOfWord 0x40BE9162D0D88419, ratOfWord 0x4100579AB0B75E98, ratOfWord 0x4125F65372869C19, ratOfWord 0x412457D27719AD5C, ratOfWord 0xC111F9690EA5AA18]

theorem check_p8_0 :
    ratioCheckI (toInt 132 (pE seg1_3_1 pr8 ps8)) (toInt 52 (sTilde seg1_3_1.c ps8)) 132 52 68 282 (-1) (1) 1 12 = true ∧
      isScaled 132 (pE seg1_3_1 pr8 ps8) = true ∧ isScaled 52 (sTilde seg1_3_1.c ps8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 1 = 8 - seg1_3_1.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 1 = 9 - seg1_3_1.c ∧
      0 < (8 : ℚ) ∧ seg1_3_1.a ≤ 8 ∧ 9 ≤ seg1_3_1.b := by
  decide +kernel

theorem check_p8_1 :
    ratioCheckI (toInt 132 (pE seg1_3_2 pr8 ps8)) (toInt 52 (sTilde seg1_3_2.c ps8)) 132 52 68 282 (-1) (1) 1 12 = true ∧
      isScaled 132 (pE seg1_3_2 pr8 ps8) = true ∧ isScaled 52 (sTilde seg1_3_2.c ps8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 1 = 9 - seg1_3_2.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 1 = 10 - seg1_3_2.c ∧
      0 < (9 : ℚ) ∧ seg1_3_2.a ≤ 9 ∧ 10 ≤ seg1_3_2.b := by
  decide +kernel

theorem check_p8_2 :
    ratioCheckI (toInt 148 (pE seg1_4_0 pr8 ps8)) (toInt 68 (sTilde seg1_4_0.c ps8)) 148 68 68 282 (-5) (5) 3 12 = true ∧
      isScaled 148 (pE seg1_4_0 pr8 ps8) = true ∧ isScaled 68 (sTilde seg1_4_0.c ps8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 10 - seg1_4_0.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 45 / 2 ^ 2 - seg1_4_0.c ∧
      0 < (10 : ℚ) ∧ seg1_4_0.a ≤ 10 ∧ 45 / 2 ^ 2 ≤ seg1_4_0.b := by
  decide +kernel

theorem check_p8_3 :
    ratioCheckI (toInt 148 (pE seg1_4_1 pr8 ps8)) (toInt 68 (sTilde seg1_4_1.c ps8)) 148 68 68 282 (-5) (5) 3 12 = true ∧
      isScaled 148 (pE seg1_4_1 pr8 ps8) = true ∧ isScaled 68 (sTilde seg1_4_1.c ps8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 45 / 2 ^ 2 - seg1_4_1.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 25 / 2 ^ 1 - seg1_4_1.c ∧
      0 < (45 / 2 ^ 2 : ℚ) ∧ seg1_4_1.a ≤ 45 / 2 ^ 2 ∧ 25 / 2 ^ 1 ≤ seg1_4_1.b := by
  decide +kernel

theorem check_p8_4 :
    ratioCheckI (toInt 148 (pE seg1_4_2 pr8 ps8)) (toInt 68 (sTilde seg1_4_2.c ps8)) 148 68 68 282 (-5) (5) 3 12 = true ∧
      isScaled 148 (pE seg1_4_2 pr8 ps8) = true ∧ isScaled 68 (sTilde seg1_4_2.c ps8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 25 / 2 ^ 1 - seg1_4_2.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 55 / 2 ^ 2 - seg1_4_2.c ∧
      0 < (25 / 2 ^ 1 : ℚ) ∧ seg1_4_2.a ≤ 25 / 2 ^ 1 ∧ 55 / 2 ^ 2 ≤ seg1_4_2.b := by
  decide +kernel

theorem check_p8_5 :
    ratioCheckI (toInt 148 (pE seg1_4_3 pr8 ps8)) (toInt 68 (sTilde seg1_4_3.c ps8)) 148 68 68 282 (-5) (5) 3 12 = true ∧
      isScaled 148 (pE seg1_4_3 pr8 ps8) = true ∧ isScaled 68 (sTilde seg1_4_3.c ps8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 55 / 2 ^ 2 - seg1_4_3.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 15 - seg1_4_3.c ∧
      0 < (55 / 2 ^ 2 : ℚ) ∧ seg1_4_3.a ≤ 55 / 2 ^ 2 ∧ 15 ≤ seg1_4_3.b := by
  decide +kernel

theorem check_p8_6 :
    ratioCheckI (toInt 148 (pE seg1_5_0 pr8 ps8)) (toInt 68 (sTilde seg1_5_0.c ps8)) 148 68 68 282 (-7) (7) 3 12 = true ∧
      isScaled 148 (pE seg1_5_0 pr8 ps8) = true ∧ isScaled 68 (sTilde seg1_5_0.c ps8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 15 - seg1_5_0.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 67 / 2 ^ 2 - seg1_5_0.c ∧
      0 < (15 : ℚ) ∧ seg1_5_0.a ≤ 15 ∧ 67 / 2 ^ 2 ≤ seg1_5_0.b := by
  decide +kernel

theorem check_p8_7 :
    ratioCheckI (toInt 148 (pE seg1_5_1 pr8 ps8)) (toInt 68 (sTilde seg1_5_1.c ps8)) 148 68 68 282 (-7) (7) 3 12 = true ∧
      isScaled 148 (pE seg1_5_1 pr8 ps8) = true ∧ isScaled 68 (sTilde seg1_5_1.c ps8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 67 / 2 ^ 2 - seg1_5_1.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 37 / 2 ^ 1 - seg1_5_1.c ∧
      0 < (67 / 2 ^ 2 : ℚ) ∧ seg1_5_1.a ≤ 67 / 2 ^ 2 ∧ 37 / 2 ^ 1 ≤ seg1_5_1.b := by
  decide +kernel

theorem check_p8_8 :
    ratioCheckI (toInt 148 (pE seg1_5_2 pr8 ps8)) (toInt 68 (sTilde seg1_5_2.c ps8)) 148 68 68 282 (-7) (7) 3 12 = true ∧
      isScaled 148 (pE seg1_5_2 pr8 ps8) = true ∧ isScaled 68 (sTilde seg1_5_2.c ps8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 37 / 2 ^ 1 - seg1_5_2.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 81 / 2 ^ 2 - seg1_5_2.c ∧
      0 < (37 / 2 ^ 1 : ℚ) ∧ seg1_5_2.a ≤ 37 / 2 ^ 1 ∧ 81 / 2 ^ 2 ≤ seg1_5_2.b := by
  decide +kernel

theorem check_p8_9 :
    ratioCheckI (toInt 148 (pE seg1_5_3 pr8 ps8)) (toInt 68 (sTilde seg1_5_3.c ps8)) 148 68 68 282 (-7) (7) 3 12 = true ∧
      isScaled 148 (pE seg1_5_3 pr8 ps8) = true ∧ isScaled 68 (sTilde seg1_5_3.c ps8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 81 / 2 ^ 2 - seg1_5_3.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 22 - seg1_5_3.c ∧
      0 < (81 / 2 ^ 2 : ℚ) ∧ seg1_5_3.a ≤ 81 / 2 ^ 2 ∧ 22 ≤ seg1_5_3.b := by
  decide +kernel

theorem check_p8_10 :
    ratioCheckI (toInt 124 (pE seg1_6_0 pr8 ps8)) (toInt 44 (sTilde seg1_6_0.c ps8)) 124 44 68 282 (-1) (1) 0 12 = true ∧
      isScaled 124 (pE seg1_6_0 pr8 ps8) = true ∧ isScaled 44 (sTilde seg1_6_0.c ps8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 22 - seg1_6_0.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 24 - seg1_6_0.c ∧
      0 < (22 : ℚ) ∧ seg1_6_0.a ≤ 22 ∧ 24 ≤ seg1_6_0.b := by
  decide +kernel

theorem check_p8_11 :
    ratioCheckI (toInt 124 (pE seg1_6_1 pr8 ps8)) (toInt 44 (sTilde seg1_6_1.c ps8)) 124 44 68 282 (-1) (1) 0 12 = true ∧
      isScaled 124 (pE seg1_6_1 pr8 ps8) = true ∧ isScaled 44 (sTilde seg1_6_1.c ps8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 24 - seg1_6_1.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 26 - seg1_6_1.c ∧
      0 < (24 : ℚ) ∧ seg1_6_1.a ≤ 24 ∧ 26 ≤ seg1_6_1.b := by
  decide +kernel

theorem check_p8_12 :
    ratioCheckI (toInt 124 (pE seg1_6_2 pr8 ps8)) (toInt 44 (sTilde seg1_6_2.c ps8)) 124 44 68 282 (-1) (1) 0 12 = true ∧
      isScaled 124 (pE seg1_6_2 pr8 ps8) = true ∧ isScaled 44 (sTilde seg1_6_2.c ps8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 26 - seg1_6_2.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 28 - seg1_6_2.c ∧
      0 < (26 : ℚ) ∧ seg1_6_2.a ≤ 26 ∧ 28 ≤ seg1_6_2.b := by
  decide +kernel

theorem check_p8_13 :
    ratioCheckI (toInt 124 (pE seg1_6_3 pr8 ps8)) (toInt 44 (sTilde seg1_6_3.c ps8)) 124 44 68 282 (-1) (1) 0 12 = true ∧
      isScaled 124 (pE seg1_6_3 pr8 ps8) = true ∧ isScaled 44 (sTilde seg1_6_3.c ps8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 28 - seg1_6_3.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 30 - seg1_6_3.c ∧
      0 < (28 : ℚ) ∧ seg1_6_3.a ≤ 28 ∧ 30 ≤ seg1_6_3.b := by
  decide +kernel

theorem check_p8_asym :
    ratioCheckI (toInt 78 (pEa casym pr8 ps8)) (toInt 44 (sAsym ps8)) 78 44 68 282 0 35 10 12 = true ∧
      isScaled 78 (pEa casym pr8 ps8) = true ∧ isScaled 44 (sAsym ps8) = true := by
  decide +kernel

/-- `pone` on `[8, ∞)`: within `282/2^68 + 2^-70`, about `2 ^ -59.86`. -/
theorem pone_8 (x : ℝ) (hlo : (((8 : ℚ)) : ℝ) ≤ x) :
    |P1 x - pFd pr8 ps8 x| ≤ 282 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : pr8.length ≤ ps8.length + 1 := by decide
  rcases le_total x (((9 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast p_step (piece1_3, seg1_3_1) (segs_3_ok.2.1) (by simp [pieces, last]) pr8 ps8 hR (8) (9) 132 52 282 _ _ _ ⟨check_p8_0.2.1, check_p8_0.2.2.1⟩ check_p8_0.1 ⟨check_p8_0.2.2.2.1, check_p8_0.2.2.2.2.1⟩ check_p8_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((10 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast p_step (piece1_3, seg1_3_2) (segs_3_ok.2.2) (by simp [pieces, last]) pr8 ps8 hR (9) (10) 132 52 282 _ _ _ ⟨check_p8_1.2.1, check_p8_1.2.2.1⟩ check_p8_1.1 ⟨check_p8_1.2.2.2.1, check_p8_1.2.2.2.2.1⟩ check_p8_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((45 / 2 ^ 2 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast p_step (piece1_4, seg1_4_0) (segs_4_ok.1) (by simp [pieces, last]) pr8 ps8 hR (10) (45 / 2 ^ 2) 148 68 282 _ _ _ ⟨check_p8_2.2.1, check_p8_2.2.2.1⟩ check_p8_2.1 ⟨check_p8_2.2.2.2.1, check_p8_2.2.2.2.2.1⟩ check_p8_2.2.2.2.2.2 x ⟨h1, h2⟩
  rcases le_total x (((25 / 2 ^ 1 : ℚ)) : ℝ) with h3 | h3
  · exact_mod_cast p_step (piece1_4, seg1_4_1) (segs_4_ok.2.1) (by simp [pieces, last]) pr8 ps8 hR (45 / 2 ^ 2) (25 / 2 ^ 1) 148 68 282 _ _ _ ⟨check_p8_3.2.1, check_p8_3.2.2.1⟩ check_p8_3.1 ⟨check_p8_3.2.2.2.1, check_p8_3.2.2.2.2.1⟩ check_p8_3.2.2.2.2.2 x ⟨h2, h3⟩
  rcases le_total x (((55 / 2 ^ 2 : ℚ)) : ℝ) with h4 | h4
  · exact_mod_cast p_step (piece1_4, seg1_4_2) (segs_4_ok.2.2.1) (by simp [pieces, last]) pr8 ps8 hR (25 / 2 ^ 1) (55 / 2 ^ 2) 148 68 282 _ _ _ ⟨check_p8_4.2.1, check_p8_4.2.2.1⟩ check_p8_4.1 ⟨check_p8_4.2.2.2.1, check_p8_4.2.2.2.2.1⟩ check_p8_4.2.2.2.2.2 x ⟨h3, h4⟩
  rcases le_total x (((15 : ℚ)) : ℝ) with h5 | h5
  · exact_mod_cast p_step (piece1_4, seg1_4_3) (segs_4_ok.2.2.2) (by simp [pieces, last]) pr8 ps8 hR (55 / 2 ^ 2) (15) 148 68 282 _ _ _ ⟨check_p8_5.2.1, check_p8_5.2.2.1⟩ check_p8_5.1 ⟨check_p8_5.2.2.2.1, check_p8_5.2.2.2.2.1⟩ check_p8_5.2.2.2.2.2 x ⟨h4, h5⟩
  rcases le_total x (((67 / 2 ^ 2 : ℚ)) : ℝ) with h6 | h6
  · exact_mod_cast p_step (piece1_5, seg1_5_0) (segs_5_ok.1) (by simp [pieces, last]) pr8 ps8 hR (15) (67 / 2 ^ 2) 148 68 282 _ _ _ ⟨check_p8_6.2.1, check_p8_6.2.2.1⟩ check_p8_6.1 ⟨check_p8_6.2.2.2.1, check_p8_6.2.2.2.2.1⟩ check_p8_6.2.2.2.2.2 x ⟨h5, h6⟩
  rcases le_total x (((37 / 2 ^ 1 : ℚ)) : ℝ) with h7 | h7
  · exact_mod_cast p_step (piece1_5, seg1_5_1) (segs_5_ok.2.1) (by simp [pieces, last]) pr8 ps8 hR (67 / 2 ^ 2) (37 / 2 ^ 1) 148 68 282 _ _ _ ⟨check_p8_7.2.1, check_p8_7.2.2.1⟩ check_p8_7.1 ⟨check_p8_7.2.2.2.1, check_p8_7.2.2.2.2.1⟩ check_p8_7.2.2.2.2.2 x ⟨h6, h7⟩
  rcases le_total x (((81 / 2 ^ 2 : ℚ)) : ℝ) with h8 | h8
  · exact_mod_cast p_step (piece1_5, seg1_5_2) (segs_5_ok.2.2.1) (by simp [pieces, last]) pr8 ps8 hR (37 / 2 ^ 1) (81 / 2 ^ 2) 148 68 282 _ _ _ ⟨check_p8_8.2.1, check_p8_8.2.2.1⟩ check_p8_8.1 ⟨check_p8_8.2.2.2.1, check_p8_8.2.2.2.2.1⟩ check_p8_8.2.2.2.2.2 x ⟨h7, h8⟩
  rcases le_total x (((22 : ℚ)) : ℝ) with h9 | h9
  · exact_mod_cast p_step (piece1_5, seg1_5_3) (segs_5_ok.2.2.2) (by simp [pieces, last]) pr8 ps8 hR (81 / 2 ^ 2) (22) 148 68 282 _ _ _ ⟨check_p8_9.2.1, check_p8_9.2.2.1⟩ check_p8_9.1 ⟨check_p8_9.2.2.2.1, check_p8_9.2.2.2.2.1⟩ check_p8_9.2.2.2.2.2 x ⟨h8, h9⟩
  rcases le_total x (((24 : ℚ)) : ℝ) with h10 | h10
  · exact_mod_cast p_step (piece1_6, seg1_6_0) (segs_6_ok.1) (by simp [pieces, last]) pr8 ps8 hR (22) (24) 124 44 282 _ _ _ ⟨check_p8_10.2.1, check_p8_10.2.2.1⟩ check_p8_10.1 ⟨check_p8_10.2.2.2.1, check_p8_10.2.2.2.2.1⟩ check_p8_10.2.2.2.2.2 x ⟨h9, h10⟩
  rcases le_total x (((26 : ℚ)) : ℝ) with h11 | h11
  · exact_mod_cast p_step (piece1_6, seg1_6_1) (segs_6_ok.2.1) (by simp [pieces, last]) pr8 ps8 hR (24) (26) 124 44 282 _ _ _ ⟨check_p8_11.2.1, check_p8_11.2.2.1⟩ check_p8_11.1 ⟨check_p8_11.2.2.2.1, check_p8_11.2.2.2.2.1⟩ check_p8_11.2.2.2.2.2 x ⟨h10, h11⟩
  rcases le_total x (((28 : ℚ)) : ℝ) with h12 | h12
  · exact_mod_cast p_step (piece1_6, seg1_6_2) (segs_6_ok.2.2.1) (by simp [pieces, last]) pr8 ps8 hR (26) (28) 124 44 282 _ _ _ ⟨check_p8_12.2.1, check_p8_12.2.2.1⟩ check_p8_12.1 ⟨check_p8_12.2.2.2.1, check_p8_12.2.2.2.2.1⟩ check_p8_12.2.2.2.2.2 x ⟨h11, h12⟩
  rcases le_total x (((30 : ℚ)) : ℝ) with h13 | h13
  · exact_mod_cast p_step (piece1_6, seg1_6_3) (segs_6_ok.2.2.2) (by simp [pieces, last]) pr8 ps8 hR (28) (30) 124 44 282 _ _ _ ⟨check_p8_13.2.1, check_p8_13.2.2.1⟩ check_p8_13.1 ⟨check_p8_13.2.2.2.1, check_p8_13.2.2.2.2.1⟩ check_p8_13.2.2.2.2.2 x ⟨h12, h13⟩
  exact_mod_cast p_asym_step pr8 ps8 78 44 282 check_p8_asym.2 check_p8_asym.1 x (by exact_mod_cast h13)

theorem check_q8_0 :
    ratioCheckI (toInt 136 (qE (3 / 8) seg1_3_1 qr8 qs8)) (toInt 56 (qW seg1_3_1 qs8)) 136 56 68 20 (-1) (1) 1 12 = true ∧
      isScaled 136 (qE (3 / 8) seg1_3_1 qr8 qs8) = true ∧ isScaled 56 (qW seg1_3_1 qs8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 1 = 8 - seg1_3_1.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 1 = 9 - seg1_3_1.c ∧
      0 < (8 : ℚ) ∧ seg1_3_1.a ≤ 8 ∧ 9 ≤ seg1_3_1.b := by
  decide +kernel

theorem check_q8_1 :
    ratioCheckI (toInt 136 (qE (3 / 8) seg1_3_2 qr8 qs8)) (toInt 56 (qW seg1_3_2 qs8)) 136 56 68 20 (-1) (1) 1 12 = true ∧
      isScaled 136 (qE (3 / 8) seg1_3_2 qr8 qs8) = true ∧ isScaled 56 (qW seg1_3_2 qs8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 1 = 9 - seg1_3_2.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 1 = 10 - seg1_3_2.c ∧
      0 < (9 : ℚ) ∧ seg1_3_2.a ≤ 9 ∧ 10 ≤ seg1_3_2.b := by
  decide +kernel

theorem check_q8_2 :
    ratioCheckI (toInt 158 (qE (3 / 8) seg1_4_0 qr8 qs8)) (toInt 78 (qW seg1_4_0 qs8)) 158 78 68 20 (-5) (5) 3 12 = true ∧
      isScaled 158 (qE (3 / 8) seg1_4_0 qr8 qs8) = true ∧ isScaled 78 (qW seg1_4_0 qs8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 10 - seg1_4_0.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 45 / 2 ^ 2 - seg1_4_0.c ∧
      0 < (10 : ℚ) ∧ seg1_4_0.a ≤ 10 ∧ 45 / 2 ^ 2 ≤ seg1_4_0.b := by
  decide +kernel

theorem check_q8_3 :
    ratioCheckI (toInt 158 (qE (3 / 8) seg1_4_1 qr8 qs8)) (toInt 78 (qW seg1_4_1 qs8)) 158 78 68 20 (-5) (5) 3 12 = true ∧
      isScaled 158 (qE (3 / 8) seg1_4_1 qr8 qs8) = true ∧ isScaled 78 (qW seg1_4_1 qs8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 45 / 2 ^ 2 - seg1_4_1.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 25 / 2 ^ 1 - seg1_4_1.c ∧
      0 < (45 / 2 ^ 2 : ℚ) ∧ seg1_4_1.a ≤ 45 / 2 ^ 2 ∧ 25 / 2 ^ 1 ≤ seg1_4_1.b := by
  decide +kernel

theorem check_q8_4 :
    ratioCheckI (toInt 158 (qE (3 / 8) seg1_4_2 qr8 qs8)) (toInt 78 (qW seg1_4_2 qs8)) 158 78 68 20 (-5) (5) 3 12 = true ∧
      isScaled 158 (qE (3 / 8) seg1_4_2 qr8 qs8) = true ∧ isScaled 78 (qW seg1_4_2 qs8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 25 / 2 ^ 1 - seg1_4_2.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 55 / 2 ^ 2 - seg1_4_2.c ∧
      0 < (25 / 2 ^ 1 : ℚ) ∧ seg1_4_2.a ≤ 25 / 2 ^ 1 ∧ 55 / 2 ^ 2 ≤ seg1_4_2.b := by
  decide +kernel

theorem check_q8_5 :
    ratioCheckI (toInt 158 (qE (3 / 8) seg1_4_3 qr8 qs8)) (toInt 78 (qW seg1_4_3 qs8)) 158 78 68 20 (-5) (5) 3 12 = true ∧
      isScaled 158 (qE (3 / 8) seg1_4_3 qr8 qs8) = true ∧ isScaled 78 (qW seg1_4_3 qs8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 55 / 2 ^ 2 - seg1_4_3.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 15 - seg1_4_3.c ∧
      0 < (55 / 2 ^ 2 : ℚ) ∧ seg1_4_3.a ≤ 55 / 2 ^ 2 ∧ 15 ≤ seg1_4_3.b := by
  decide +kernel

theorem check_q8_6 :
    ratioCheckI (toInt 158 (qE (3 / 8) seg1_5_0 qr8 qs8)) (toInt 78 (qW seg1_5_0 qs8)) 158 78 68 20 (-7) (7) 3 12 = true ∧
      isScaled 158 (qE (3 / 8) seg1_5_0 qr8 qs8) = true ∧ isScaled 78 (qW seg1_5_0 qs8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 15 - seg1_5_0.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 67 / 2 ^ 2 - seg1_5_0.c ∧
      0 < (15 : ℚ) ∧ seg1_5_0.a ≤ 15 ∧ 67 / 2 ^ 2 ≤ seg1_5_0.b := by
  decide +kernel

theorem check_q8_7 :
    ratioCheckI (toInt 158 (qE (3 / 8) seg1_5_1 qr8 qs8)) (toInt 78 (qW seg1_5_1 qs8)) 158 78 68 20 (-7) (7) 3 12 = true ∧
      isScaled 158 (qE (3 / 8) seg1_5_1 qr8 qs8) = true ∧ isScaled 78 (qW seg1_5_1 qs8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 67 / 2 ^ 2 - seg1_5_1.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 37 / 2 ^ 1 - seg1_5_1.c ∧
      0 < (67 / 2 ^ 2 : ℚ) ∧ seg1_5_1.a ≤ 67 / 2 ^ 2 ∧ 37 / 2 ^ 1 ≤ seg1_5_1.b := by
  decide +kernel

theorem check_q8_8 :
    ratioCheckI (toInt 158 (qE (3 / 8) seg1_5_2 qr8 qs8)) (toInt 78 (qW seg1_5_2 qs8)) 158 78 68 20 (-7) (7) 3 12 = true ∧
      isScaled 158 (qE (3 / 8) seg1_5_2 qr8 qs8) = true ∧ isScaled 78 (qW seg1_5_2 qs8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 37 / 2 ^ 1 - seg1_5_2.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 81 / 2 ^ 2 - seg1_5_2.c ∧
      0 < (37 / 2 ^ 1 : ℚ) ∧ seg1_5_2.a ≤ 37 / 2 ^ 1 ∧ 81 / 2 ^ 2 ≤ seg1_5_2.b := by
  decide +kernel

theorem check_q8_9 :
    ratioCheckI (toInt 158 (qE (3 / 8) seg1_5_3 qr8 qs8)) (toInt 78 (qW seg1_5_3 qs8)) 158 78 68 20 (-7) (7) 3 12 = true ∧
      isScaled 158 (qE (3 / 8) seg1_5_3 qr8 qs8) = true ∧ isScaled 78 (qW seg1_5_3 qs8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 81 / 2 ^ 2 - seg1_5_3.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 22 - seg1_5_3.c ∧
      0 < (81 / 2 ^ 2 : ℚ) ∧ seg1_5_3.a ≤ 81 / 2 ^ 2 ∧ 22 ≤ seg1_5_3.b := by
  decide +kernel

theorem check_q8_10 :
    ratioCheckI (toInt 125 (qE (3 / 8) seg1_6_0 qr8 qs8)) (toInt 45 (qW seg1_6_0 qs8)) 125 45 68 20 (-1) (1) 0 12 = true ∧
      isScaled 125 (qE (3 / 8) seg1_6_0 qr8 qs8) = true ∧ isScaled 45 (qW seg1_6_0 qs8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 22 - seg1_6_0.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 24 - seg1_6_0.c ∧
      0 < (22 : ℚ) ∧ seg1_6_0.a ≤ 22 ∧ 24 ≤ seg1_6_0.b := by
  decide +kernel

theorem check_q8_11 :
    ratioCheckI (toInt 125 (qE (3 / 8) seg1_6_1 qr8 qs8)) (toInt 45 (qW seg1_6_1 qs8)) 125 45 68 20 (-1) (1) 0 12 = true ∧
      isScaled 125 (qE (3 / 8) seg1_6_1 qr8 qs8) = true ∧ isScaled 45 (qW seg1_6_1 qs8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 24 - seg1_6_1.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 26 - seg1_6_1.c ∧
      0 < (24 : ℚ) ∧ seg1_6_1.a ≤ 24 ∧ 26 ≤ seg1_6_1.b := by
  decide +kernel

theorem check_q8_12 :
    ratioCheckI (toInt 125 (qE (3 / 8) seg1_6_2 qr8 qs8)) (toInt 45 (qW seg1_6_2 qs8)) 125 45 68 20 (-1) (1) 0 12 = true ∧
      isScaled 125 (qE (3 / 8) seg1_6_2 qr8 qs8) = true ∧ isScaled 45 (qW seg1_6_2 qs8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 26 - seg1_6_2.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 28 - seg1_6_2.c ∧
      0 < (26 : ℚ) ∧ seg1_6_2.a ≤ 26 ∧ 28 ≤ seg1_6_2.b := by
  decide +kernel

theorem check_q8_13 :
    ratioCheckI (toInt 125 (qE (3 / 8) seg1_6_3 qr8 qs8)) (toInt 45 (qW seg1_6_3 qs8)) 125 45 68 20 (-1) (1) 0 12 = true ∧
      isScaled 125 (qE (3 / 8) seg1_6_3 qr8 qs8) = true ∧ isScaled 45 (qW seg1_6_3 qs8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 28 - seg1_6_3.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 30 - seg1_6_3.c ∧
      0 < (28 : ℚ) ∧ seg1_6_3.a ≤ 28 ∧ 30 ≤ seg1_6_3.b := by
  decide +kernel

theorem check_q8_asym :
    ratioCheckI (toInt 79 (qEa (3 / 8) casym qr8 qs8)) (toInt 45 (sAsym qs8)) 79 45 68 20 0 35 10 12 = true ∧
      isScaled 79 (qEa (3 / 8) casym qr8 qs8) = true ∧ isScaled 45 (sAsym qs8) = true := by
  decide +kernel

/-- `qone` on `[8, ∞)`: within `20/2^68 + 2^-70`, about `2 ^ -63.66`. -/
theorem qone_8 (x : ℝ) (hlo : (((8 : ℚ)) : ℝ) ≤ x) :
    |Q1 x - qFd (3 / 8) qr8 qs8 x| ≤ 20 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : qr8.length ≤ qs8.length + 1 := by decide
  rcases le_total x (((9 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast q_step (piece1_3, seg1_3_1) (segs_3_ok.2.1) (by simp [pieces, last]) qr8 qs8 hR (8) (9) 136 56 20 _ _ _ ⟨check_q8_0.2.1, check_q8_0.2.2.1⟩ check_q8_0.1 ⟨check_q8_0.2.2.2.1, check_q8_0.2.2.2.2.1⟩ check_q8_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((10 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast q_step (piece1_3, seg1_3_2) (segs_3_ok.2.2) (by simp [pieces, last]) qr8 qs8 hR (9) (10) 136 56 20 _ _ _ ⟨check_q8_1.2.1, check_q8_1.2.2.1⟩ check_q8_1.1 ⟨check_q8_1.2.2.2.1, check_q8_1.2.2.2.2.1⟩ check_q8_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((45 / 2 ^ 2 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast q_step (piece1_4, seg1_4_0) (segs_4_ok.1) (by simp [pieces, last]) qr8 qs8 hR (10) (45 / 2 ^ 2) 158 78 20 _ _ _ ⟨check_q8_2.2.1, check_q8_2.2.2.1⟩ check_q8_2.1 ⟨check_q8_2.2.2.2.1, check_q8_2.2.2.2.2.1⟩ check_q8_2.2.2.2.2.2 x ⟨h1, h2⟩
  rcases le_total x (((25 / 2 ^ 1 : ℚ)) : ℝ) with h3 | h3
  · exact_mod_cast q_step (piece1_4, seg1_4_1) (segs_4_ok.2.1) (by simp [pieces, last]) qr8 qs8 hR (45 / 2 ^ 2) (25 / 2 ^ 1) 158 78 20 _ _ _ ⟨check_q8_3.2.1, check_q8_3.2.2.1⟩ check_q8_3.1 ⟨check_q8_3.2.2.2.1, check_q8_3.2.2.2.2.1⟩ check_q8_3.2.2.2.2.2 x ⟨h2, h3⟩
  rcases le_total x (((55 / 2 ^ 2 : ℚ)) : ℝ) with h4 | h4
  · exact_mod_cast q_step (piece1_4, seg1_4_2) (segs_4_ok.2.2.1) (by simp [pieces, last]) qr8 qs8 hR (25 / 2 ^ 1) (55 / 2 ^ 2) 158 78 20 _ _ _ ⟨check_q8_4.2.1, check_q8_4.2.2.1⟩ check_q8_4.1 ⟨check_q8_4.2.2.2.1, check_q8_4.2.2.2.2.1⟩ check_q8_4.2.2.2.2.2 x ⟨h3, h4⟩
  rcases le_total x (((15 : ℚ)) : ℝ) with h5 | h5
  · exact_mod_cast q_step (piece1_4, seg1_4_3) (segs_4_ok.2.2.2) (by simp [pieces, last]) qr8 qs8 hR (55 / 2 ^ 2) (15) 158 78 20 _ _ _ ⟨check_q8_5.2.1, check_q8_5.2.2.1⟩ check_q8_5.1 ⟨check_q8_5.2.2.2.1, check_q8_5.2.2.2.2.1⟩ check_q8_5.2.2.2.2.2 x ⟨h4, h5⟩
  rcases le_total x (((67 / 2 ^ 2 : ℚ)) : ℝ) with h6 | h6
  · exact_mod_cast q_step (piece1_5, seg1_5_0) (segs_5_ok.1) (by simp [pieces, last]) qr8 qs8 hR (15) (67 / 2 ^ 2) 158 78 20 _ _ _ ⟨check_q8_6.2.1, check_q8_6.2.2.1⟩ check_q8_6.1 ⟨check_q8_6.2.2.2.1, check_q8_6.2.2.2.2.1⟩ check_q8_6.2.2.2.2.2 x ⟨h5, h6⟩
  rcases le_total x (((37 / 2 ^ 1 : ℚ)) : ℝ) with h7 | h7
  · exact_mod_cast q_step (piece1_5, seg1_5_1) (segs_5_ok.2.1) (by simp [pieces, last]) qr8 qs8 hR (67 / 2 ^ 2) (37 / 2 ^ 1) 158 78 20 _ _ _ ⟨check_q8_7.2.1, check_q8_7.2.2.1⟩ check_q8_7.1 ⟨check_q8_7.2.2.2.1, check_q8_7.2.2.2.2.1⟩ check_q8_7.2.2.2.2.2 x ⟨h6, h7⟩
  rcases le_total x (((81 / 2 ^ 2 : ℚ)) : ℝ) with h8 | h8
  · exact_mod_cast q_step (piece1_5, seg1_5_2) (segs_5_ok.2.2.1) (by simp [pieces, last]) qr8 qs8 hR (37 / 2 ^ 1) (81 / 2 ^ 2) 158 78 20 _ _ _ ⟨check_q8_8.2.1, check_q8_8.2.2.1⟩ check_q8_8.1 ⟨check_q8_8.2.2.2.1, check_q8_8.2.2.2.2.1⟩ check_q8_8.2.2.2.2.2 x ⟨h7, h8⟩
  rcases le_total x (((22 : ℚ)) : ℝ) with h9 | h9
  · exact_mod_cast q_step (piece1_5, seg1_5_3) (segs_5_ok.2.2.2) (by simp [pieces, last]) qr8 qs8 hR (81 / 2 ^ 2) (22) 158 78 20 _ _ _ ⟨check_q8_9.2.1, check_q8_9.2.2.1⟩ check_q8_9.1 ⟨check_q8_9.2.2.2.1, check_q8_9.2.2.2.2.1⟩ check_q8_9.2.2.2.2.2 x ⟨h8, h9⟩
  rcases le_total x (((24 : ℚ)) : ℝ) with h10 | h10
  · exact_mod_cast q_step (piece1_6, seg1_6_0) (segs_6_ok.1) (by simp [pieces, last]) qr8 qs8 hR (22) (24) 125 45 20 _ _ _ ⟨check_q8_10.2.1, check_q8_10.2.2.1⟩ check_q8_10.1 ⟨check_q8_10.2.2.2.1, check_q8_10.2.2.2.2.1⟩ check_q8_10.2.2.2.2.2 x ⟨h9, h10⟩
  rcases le_total x (((26 : ℚ)) : ℝ) with h11 | h11
  · exact_mod_cast q_step (piece1_6, seg1_6_1) (segs_6_ok.2.1) (by simp [pieces, last]) qr8 qs8 hR (24) (26) 125 45 20 _ _ _ ⟨check_q8_11.2.1, check_q8_11.2.2.1⟩ check_q8_11.1 ⟨check_q8_11.2.2.2.1, check_q8_11.2.2.2.2.1⟩ check_q8_11.2.2.2.2.2 x ⟨h10, h11⟩
  rcases le_total x (((28 : ℚ)) : ℝ) with h12 | h12
  · exact_mod_cast q_step (piece1_6, seg1_6_2) (segs_6_ok.2.2.1) (by simp [pieces, last]) qr8 qs8 hR (26) (28) 125 45 20 _ _ _ ⟨check_q8_12.2.1, check_q8_12.2.2.1⟩ check_q8_12.1 ⟨check_q8_12.2.2.2.1, check_q8_12.2.2.2.2.1⟩ check_q8_12.2.2.2.2.2 x ⟨h11, h12⟩
  rcases le_total x (((30 : ℚ)) : ℝ) with h13 | h13
  · exact_mod_cast q_step (piece1_6, seg1_6_3) (segs_6_ok.2.2.2) (by simp [pieces, last]) qr8 qs8 hR (28) (30) 125 45 20 _ _ _ ⟨check_q8_13.2.1, check_q8_13.2.2.1⟩ check_q8_13.1 ⟨check_q8_13.2.2.2.1, check_q8_13.2.2.2.2.1⟩ check_q8_13.2.2.2.2.2 x ⟨h12, h13⟩
  exact_mod_cast q_asym_step qr8 qs8 79 45 20 check_q8_asym.2 check_q8_asym.1 x (by exact_mod_cast h13)

#print axioms pone_8
#print axioms qone_8

end LeanExe.ProofKit.BesselFd1b
