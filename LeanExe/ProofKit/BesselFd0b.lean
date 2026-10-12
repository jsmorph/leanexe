import LeanExe.ProofKit.BesselSeg0

/-!
fdlibm's rational approximations `pzero` and `qzero` of `P0` and `Q0` from `e_j0.c` (FreeBSD msun
at commit `20381bce4b63975494a2f4bc84257f6932e6d379`) on the ranges that start at
`8`, where `b3 = 0x4006DB6D00000000` (about 2.8571) and
`b5 = 0x40122E8B00000000` (about 4.5454) are the boundaries that `e_j0.c` tests on the high word.
`pFd R S x` and `qFd (-1/8) R S x` are fdlibm's formulas without rounding, with the coefficient lists
`ratOfWord` of the words that `e_j0.c` gives beside the decimal values.  Each theorem bounds
`|P0 x - pFd R S x|` or `|Q0 x - qFd (-1/8) R S x|` for every real `x` in the range, from one
kernel check (`ratioCheckI`) per segment of `BesselSeg0` and, from 30 on, per Hankel's expansion.
-/

namespace LeanExe.ProofKit.BesselFd0b

open Set PolyBound PolyCalc BesselPQ BesselChain BesselRatio BesselLarge0 BesselSeg0

/-- The boundary `0x4006DB6D00000000` of fdlibm's ranges. -/
def b3 : ℚ := ratOfWord 0x4006DB6D00000000

/-- The boundary `0x40122E8B00000000` of fdlibm's ranges. -/
def b5 : ℚ := ratOfWord 0x40122E8B00000000

/-- `pR8` of `e_j0.c`. -/
def pR8 : List ℚ := [ratOfWord 0x0000000000000000, ratOfWord 0xBFB1FFFFFFFFFD32, ratOfWord 0xC02029D0B44FA779, ratOfWord 0xC07011027B19E863, ratOfWord 0xC0A36A6ECD4DCAFC, ratOfWord 0xC0B4850B36CC643D]
/-- `pS8` of `e_j0.c`. -/
def pS8 : List ℚ := [ratOfWord 0x405D223307A96751, ratOfWord 0x40ADF37D50596938, ratOfWord 0x40E3D2BB6EB6B05F, ratOfWord 0x40FC810F8F9FA9BD, ratOfWord 0x40E741774F2C49DC]

/-- `qR8` of `e_j0.c`. -/
def qR8 : List ℚ := [ratOfWord 0x0000000000000000, ratOfWord 0x3FB2BFFFFFFFFE2C, ratOfWord 0x402789525BB334D6, ratOfWord 0x40816D6315301825, ratOfWord 0x40C14D993E18F46D, ratOfWord 0x40E212D40E901566]
/-- `qS8` of `e_j0.c`. -/
def qS8 : List ℚ := [ratOfWord 0x406478D5365B39BC, ratOfWord 0x40BFA2584E6B0563, ratOfWord 0x4101665254D38C3F, ratOfWord 0x412883DA83A52B43, ratOfWord 0x4129A66B28DE0B3D, ratOfWord 0xC114FD6D2C9530C5]

theorem check_p8_0 :
    ratioCheckI (toInt 134 (pE seg0_3_1 pR8 pS8)) (toInt 54 (sTilde seg0_3_1.c pS8)) 134 54 68 261 (-1) (1) 1 12 = true ∧
      isScaled 134 (pE seg0_3_1 pR8 pS8) = true ∧ isScaled 54 (sTilde seg0_3_1.c pS8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 1 = 8 - seg0_3_1.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 1 = 9 - seg0_3_1.c ∧
      0 < (8 : ℚ) ∧ seg0_3_1.a ≤ 8 ∧ 9 ≤ seg0_3_1.b := by
  decide +kernel

theorem check_p8_1 :
    ratioCheckI (toInt 134 (pE seg0_3_2 pR8 pS8)) (toInt 54 (sTilde seg0_3_2.c pS8)) 134 54 68 261 (-1) (1) 1 12 = true ∧
      isScaled 134 (pE seg0_3_2 pR8 pS8) = true ∧ isScaled 54 (sTilde seg0_3_2.c pS8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 1 = 9 - seg0_3_2.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 1 = 10 - seg0_3_2.c ∧
      0 < (9 : ℚ) ∧ seg0_3_2.a ≤ 9 ∧ 10 ≤ seg0_3_2.b := by
  decide +kernel

theorem check_p8_2 :
    ratioCheckI (toInt 150 (pE seg0_4_0 pR8 pS8)) (toInt 70 (sTilde seg0_4_0.c pS8)) 150 70 68 261 (-5) (5) 3 12 = true ∧
      isScaled 150 (pE seg0_4_0 pR8 pS8) = true ∧ isScaled 70 (sTilde seg0_4_0.c pS8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 10 - seg0_4_0.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 45 / 2 ^ 2 - seg0_4_0.c ∧
      0 < (10 : ℚ) ∧ seg0_4_0.a ≤ 10 ∧ 45 / 2 ^ 2 ≤ seg0_4_0.b := by
  decide +kernel

theorem check_p8_3 :
    ratioCheckI (toInt 150 (pE seg0_4_1 pR8 pS8)) (toInt 70 (sTilde seg0_4_1.c pS8)) 150 70 68 261 (-5) (5) 3 12 = true ∧
      isScaled 150 (pE seg0_4_1 pR8 pS8) = true ∧ isScaled 70 (sTilde seg0_4_1.c pS8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 45 / 2 ^ 2 - seg0_4_1.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 25 / 2 ^ 1 - seg0_4_1.c ∧
      0 < (45 / 2 ^ 2 : ℚ) ∧ seg0_4_1.a ≤ 45 / 2 ^ 2 ∧ 25 / 2 ^ 1 ≤ seg0_4_1.b := by
  decide +kernel

theorem check_p8_4 :
    ratioCheckI (toInt 150 (pE seg0_4_2 pR8 pS8)) (toInt 70 (sTilde seg0_4_2.c pS8)) 150 70 68 261 (-5) (5) 3 12 = true ∧
      isScaled 150 (pE seg0_4_2 pR8 pS8) = true ∧ isScaled 70 (sTilde seg0_4_2.c pS8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 25 / 2 ^ 1 - seg0_4_2.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 55 / 2 ^ 2 - seg0_4_2.c ∧
      0 < (25 / 2 ^ 1 : ℚ) ∧ seg0_4_2.a ≤ 25 / 2 ^ 1 ∧ 55 / 2 ^ 2 ≤ seg0_4_2.b := by
  decide +kernel

theorem check_p8_5 :
    ratioCheckI (toInt 150 (pE seg0_4_3 pR8 pS8)) (toInt 70 (sTilde seg0_4_3.c pS8)) 150 70 68 261 (-5) (5) 3 12 = true ∧
      isScaled 150 (pE seg0_4_3 pR8 pS8) = true ∧ isScaled 70 (sTilde seg0_4_3.c pS8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 55 / 2 ^ 2 - seg0_4_3.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 15 - seg0_4_3.c ∧
      0 < (55 / 2 ^ 2 : ℚ) ∧ seg0_4_3.a ≤ 55 / 2 ^ 2 ∧ 15 ≤ seg0_4_3.b := by
  decide +kernel

theorem check_p8_6 :
    ratioCheckI (toInt 150 (pE seg0_5_0 pR8 pS8)) (toInt 70 (sTilde seg0_5_0.c pS8)) 150 70 68 261 (-7) (7) 3 12 = true ∧
      isScaled 150 (pE seg0_5_0 pR8 pS8) = true ∧ isScaled 70 (sTilde seg0_5_0.c pS8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 15 - seg0_5_0.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 67 / 2 ^ 2 - seg0_5_0.c ∧
      0 < (15 : ℚ) ∧ seg0_5_0.a ≤ 15 ∧ 67 / 2 ^ 2 ≤ seg0_5_0.b := by
  decide +kernel

theorem check_p8_7 :
    ratioCheckI (toInt 150 (pE seg0_5_1 pR8 pS8)) (toInt 70 (sTilde seg0_5_1.c pS8)) 150 70 68 261 (-7) (7) 3 12 = true ∧
      isScaled 150 (pE seg0_5_1 pR8 pS8) = true ∧ isScaled 70 (sTilde seg0_5_1.c pS8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 67 / 2 ^ 2 - seg0_5_1.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 37 / 2 ^ 1 - seg0_5_1.c ∧
      0 < (67 / 2 ^ 2 : ℚ) ∧ seg0_5_1.a ≤ 67 / 2 ^ 2 ∧ 37 / 2 ^ 1 ≤ seg0_5_1.b := by
  decide +kernel

theorem check_p8_8 :
    ratioCheckI (toInt 150 (pE seg0_5_2 pR8 pS8)) (toInt 70 (sTilde seg0_5_2.c pS8)) 150 70 68 261 (-7) (7) 3 12 = true ∧
      isScaled 150 (pE seg0_5_2 pR8 pS8) = true ∧ isScaled 70 (sTilde seg0_5_2.c pS8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 37 / 2 ^ 1 - seg0_5_2.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 81 / 2 ^ 2 - seg0_5_2.c ∧
      0 < (37 / 2 ^ 1 : ℚ) ∧ seg0_5_2.a ≤ 37 / 2 ^ 1 ∧ 81 / 2 ^ 2 ≤ seg0_5_2.b := by
  decide +kernel

theorem check_p8_9 :
    ratioCheckI (toInt 150 (pE seg0_5_3 pR8 pS8)) (toInt 70 (sTilde seg0_5_3.c pS8)) 150 70 68 261 (-7) (7) 3 12 = true ∧
      isScaled 150 (pE seg0_5_3 pR8 pS8) = true ∧ isScaled 70 (sTilde seg0_5_3.c pS8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 81 / 2 ^ 2 - seg0_5_3.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 22 - seg0_5_3.c ∧
      0 < (81 / 2 ^ 2 : ℚ) ∧ seg0_5_3.a ≤ 81 / 2 ^ 2 ∧ 22 ≤ seg0_5_3.b := by
  decide +kernel

theorem check_p8_10 :
    ratioCheckI (toInt 126 (pE seg0_6_0 pR8 pS8)) (toInt 46 (sTilde seg0_6_0.c pS8)) 126 46 68 261 (-1) (1) 0 12 = true ∧
      isScaled 126 (pE seg0_6_0 pR8 pS8) = true ∧ isScaled 46 (sTilde seg0_6_0.c pS8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 22 - seg0_6_0.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 24 - seg0_6_0.c ∧
      0 < (22 : ℚ) ∧ seg0_6_0.a ≤ 22 ∧ 24 ≤ seg0_6_0.b := by
  decide +kernel

theorem check_p8_11 :
    ratioCheckI (toInt 126 (pE seg0_6_1 pR8 pS8)) (toInt 46 (sTilde seg0_6_1.c pS8)) 126 46 68 261 (-1) (1) 0 12 = true ∧
      isScaled 126 (pE seg0_6_1 pR8 pS8) = true ∧ isScaled 46 (sTilde seg0_6_1.c pS8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 24 - seg0_6_1.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 26 - seg0_6_1.c ∧
      0 < (24 : ℚ) ∧ seg0_6_1.a ≤ 24 ∧ 26 ≤ seg0_6_1.b := by
  decide +kernel

theorem check_p8_12 :
    ratioCheckI (toInt 126 (pE seg0_6_2 pR8 pS8)) (toInt 46 (sTilde seg0_6_2.c pS8)) 126 46 68 261 (-1) (1) 0 12 = true ∧
      isScaled 126 (pE seg0_6_2 pR8 pS8) = true ∧ isScaled 46 (sTilde seg0_6_2.c pS8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 26 - seg0_6_2.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 28 - seg0_6_2.c ∧
      0 < (26 : ℚ) ∧ seg0_6_2.a ≤ 26 ∧ 28 ≤ seg0_6_2.b := by
  decide +kernel

theorem check_p8_13 :
    ratioCheckI (toInt 126 (pE seg0_6_3 pR8 pS8)) (toInt 46 (sTilde seg0_6_3.c pS8)) 126 46 68 261 (-1) (1) 0 12 = true ∧
      isScaled 126 (pE seg0_6_3 pR8 pS8) = true ∧ isScaled 46 (sTilde seg0_6_3.c pS8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 28 - seg0_6_3.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 30 - seg0_6_3.c ∧
      0 < (28 : ℚ) ∧ seg0_6_3.a ≤ 28 ∧ 30 ≤ seg0_6_3.b := by
  decide +kernel

theorem check_p8_asym :
    ratioCheckI (toInt 81 (pEa casym pR8 pS8)) (toInt 46 (sAsym pS8)) 81 46 68 261 0 35 10 12 = true ∧
      isScaled 81 (pEa casym pR8 pS8) = true ∧ isScaled 46 (sAsym pS8) = true := by
  decide +kernel

/-- `pzero` on `[8, ∞)`: within `261/2^68 + 2^-70`, about `2 ^ -59.97`. -/
theorem pzero_8 (x : ℝ) (hlo : (((8 : ℚ)) : ℝ) ≤ x) :
    |P0 x - pFd pR8 pS8 x| ≤ 261 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : pR8.length ≤ pS8.length + 1 := by decide
  rcases le_total x (((9 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast p_step (piece0_3, seg0_3_1) (segs_3_ok.2.1) (by simp [pieces, last]) pR8 pS8 hR (8) (9) 134 54 261 _ _ _ ⟨check_p8_0.2.1, check_p8_0.2.2.1⟩ check_p8_0.1 ⟨check_p8_0.2.2.2.1, check_p8_0.2.2.2.2.1⟩ check_p8_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((10 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast p_step (piece0_3, seg0_3_2) (segs_3_ok.2.2) (by simp [pieces, last]) pR8 pS8 hR (9) (10) 134 54 261 _ _ _ ⟨check_p8_1.2.1, check_p8_1.2.2.1⟩ check_p8_1.1 ⟨check_p8_1.2.2.2.1, check_p8_1.2.2.2.2.1⟩ check_p8_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((45 / 2 ^ 2 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast p_step (piece0_4, seg0_4_0) (segs_4_ok.1) (by simp [pieces, last]) pR8 pS8 hR (10) (45 / 2 ^ 2) 150 70 261 _ _ _ ⟨check_p8_2.2.1, check_p8_2.2.2.1⟩ check_p8_2.1 ⟨check_p8_2.2.2.2.1, check_p8_2.2.2.2.2.1⟩ check_p8_2.2.2.2.2.2 x ⟨h1, h2⟩
  rcases le_total x (((25 / 2 ^ 1 : ℚ)) : ℝ) with h3 | h3
  · exact_mod_cast p_step (piece0_4, seg0_4_1) (segs_4_ok.2.1) (by simp [pieces, last]) pR8 pS8 hR (45 / 2 ^ 2) (25 / 2 ^ 1) 150 70 261 _ _ _ ⟨check_p8_3.2.1, check_p8_3.2.2.1⟩ check_p8_3.1 ⟨check_p8_3.2.2.2.1, check_p8_3.2.2.2.2.1⟩ check_p8_3.2.2.2.2.2 x ⟨h2, h3⟩
  rcases le_total x (((55 / 2 ^ 2 : ℚ)) : ℝ) with h4 | h4
  · exact_mod_cast p_step (piece0_4, seg0_4_2) (segs_4_ok.2.2.1) (by simp [pieces, last]) pR8 pS8 hR (25 / 2 ^ 1) (55 / 2 ^ 2) 150 70 261 _ _ _ ⟨check_p8_4.2.1, check_p8_4.2.2.1⟩ check_p8_4.1 ⟨check_p8_4.2.2.2.1, check_p8_4.2.2.2.2.1⟩ check_p8_4.2.2.2.2.2 x ⟨h3, h4⟩
  rcases le_total x (((15 : ℚ)) : ℝ) with h5 | h5
  · exact_mod_cast p_step (piece0_4, seg0_4_3) (segs_4_ok.2.2.2) (by simp [pieces, last]) pR8 pS8 hR (55 / 2 ^ 2) (15) 150 70 261 _ _ _ ⟨check_p8_5.2.1, check_p8_5.2.2.1⟩ check_p8_5.1 ⟨check_p8_5.2.2.2.1, check_p8_5.2.2.2.2.1⟩ check_p8_5.2.2.2.2.2 x ⟨h4, h5⟩
  rcases le_total x (((67 / 2 ^ 2 : ℚ)) : ℝ) with h6 | h6
  · exact_mod_cast p_step (piece0_5, seg0_5_0) (segs_5_ok.1) (by simp [pieces, last]) pR8 pS8 hR (15) (67 / 2 ^ 2) 150 70 261 _ _ _ ⟨check_p8_6.2.1, check_p8_6.2.2.1⟩ check_p8_6.1 ⟨check_p8_6.2.2.2.1, check_p8_6.2.2.2.2.1⟩ check_p8_6.2.2.2.2.2 x ⟨h5, h6⟩
  rcases le_total x (((37 / 2 ^ 1 : ℚ)) : ℝ) with h7 | h7
  · exact_mod_cast p_step (piece0_5, seg0_5_1) (segs_5_ok.2.1) (by simp [pieces, last]) pR8 pS8 hR (67 / 2 ^ 2) (37 / 2 ^ 1) 150 70 261 _ _ _ ⟨check_p8_7.2.1, check_p8_7.2.2.1⟩ check_p8_7.1 ⟨check_p8_7.2.2.2.1, check_p8_7.2.2.2.2.1⟩ check_p8_7.2.2.2.2.2 x ⟨h6, h7⟩
  rcases le_total x (((81 / 2 ^ 2 : ℚ)) : ℝ) with h8 | h8
  · exact_mod_cast p_step (piece0_5, seg0_5_2) (segs_5_ok.2.2.1) (by simp [pieces, last]) pR8 pS8 hR (37 / 2 ^ 1) (81 / 2 ^ 2) 150 70 261 _ _ _ ⟨check_p8_8.2.1, check_p8_8.2.2.1⟩ check_p8_8.1 ⟨check_p8_8.2.2.2.1, check_p8_8.2.2.2.2.1⟩ check_p8_8.2.2.2.2.2 x ⟨h7, h8⟩
  rcases le_total x (((22 : ℚ)) : ℝ) with h9 | h9
  · exact_mod_cast p_step (piece0_5, seg0_5_3) (segs_5_ok.2.2.2) (by simp [pieces, last]) pR8 pS8 hR (81 / 2 ^ 2) (22) 150 70 261 _ _ _ ⟨check_p8_9.2.1, check_p8_9.2.2.1⟩ check_p8_9.1 ⟨check_p8_9.2.2.2.1, check_p8_9.2.2.2.2.1⟩ check_p8_9.2.2.2.2.2 x ⟨h8, h9⟩
  rcases le_total x (((24 : ℚ)) : ℝ) with h10 | h10
  · exact_mod_cast p_step (piece0_6, seg0_6_0) (segs_6_ok.1) (by simp [pieces, last]) pR8 pS8 hR (22) (24) 126 46 261 _ _ _ ⟨check_p8_10.2.1, check_p8_10.2.2.1⟩ check_p8_10.1 ⟨check_p8_10.2.2.2.1, check_p8_10.2.2.2.2.1⟩ check_p8_10.2.2.2.2.2 x ⟨h9, h10⟩
  rcases le_total x (((26 : ℚ)) : ℝ) with h11 | h11
  · exact_mod_cast p_step (piece0_6, seg0_6_1) (segs_6_ok.2.1) (by simp [pieces, last]) pR8 pS8 hR (24) (26) 126 46 261 _ _ _ ⟨check_p8_11.2.1, check_p8_11.2.2.1⟩ check_p8_11.1 ⟨check_p8_11.2.2.2.1, check_p8_11.2.2.2.2.1⟩ check_p8_11.2.2.2.2.2 x ⟨h10, h11⟩
  rcases le_total x (((28 : ℚ)) : ℝ) with h12 | h12
  · exact_mod_cast p_step (piece0_6, seg0_6_2) (segs_6_ok.2.2.1) (by simp [pieces, last]) pR8 pS8 hR (26) (28) 126 46 261 _ _ _ ⟨check_p8_12.2.1, check_p8_12.2.2.1⟩ check_p8_12.1 ⟨check_p8_12.2.2.2.1, check_p8_12.2.2.2.2.1⟩ check_p8_12.2.2.2.2.2 x ⟨h11, h12⟩
  rcases le_total x (((30 : ℚ)) : ℝ) with h13 | h13
  · exact_mod_cast p_step (piece0_6, seg0_6_3) (segs_6_ok.2.2.2) (by simp [pieces, last]) pR8 pS8 hR (28) (30) 126 46 261 _ _ _ ⟨check_p8_13.2.1, check_p8_13.2.2.1⟩ check_p8_13.1 ⟨check_p8_13.2.2.2.1, check_p8_13.2.2.2.2.1⟩ check_p8_13.2.2.2.2.2 x ⟨h12, h13⟩
  exact_mod_cast p_asym_step pR8 pS8 81 46 261 check_p8_asym.2 check_p8_asym.1 x (by exact_mod_cast h13)

theorem check_q8_0 :
    ratioCheckI (toInt 134 (qE (-1 / 8) seg0_3_1 qR8 qS8)) (toInt 54 (qW seg0_3_1 qS8)) 134 54 68 18 (-1) (1) 1 12 = true ∧
      isScaled 134 (qE (-1 / 8) seg0_3_1 qR8 qS8) = true ∧ isScaled 54 (qW seg0_3_1 qS8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 1 = 8 - seg0_3_1.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 1 = 9 - seg0_3_1.c ∧
      0 < (8 : ℚ) ∧ seg0_3_1.a ≤ 8 ∧ 9 ≤ seg0_3_1.b := by
  decide +kernel

theorem check_q8_1 :
    ratioCheckI (toInt 134 (qE (-1 / 8) seg0_3_2 qR8 qS8)) (toInt 54 (qW seg0_3_2 qS8)) 134 54 68 18 (-1) (1) 1 12 = true ∧
      isScaled 134 (qE (-1 / 8) seg0_3_2 qR8 qS8) = true ∧ isScaled 54 (qW seg0_3_2 qS8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 1 = 9 - seg0_3_2.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 1 = 10 - seg0_3_2.c ∧
      0 < (9 : ℚ) ∧ seg0_3_2.a ≤ 9 ∧ 10 ≤ seg0_3_2.b := by
  decide +kernel

theorem check_q8_2 :
    ratioCheckI (toInt 156 (qE (-1 / 8) seg0_4_0 qR8 qS8)) (toInt 76 (qW seg0_4_0 qS8)) 156 76 68 18 (-5) (5) 3 12 = true ∧
      isScaled 156 (qE (-1 / 8) seg0_4_0 qR8 qS8) = true ∧ isScaled 76 (qW seg0_4_0 qS8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 10 - seg0_4_0.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 45 / 2 ^ 2 - seg0_4_0.c ∧
      0 < (10 : ℚ) ∧ seg0_4_0.a ≤ 10 ∧ 45 / 2 ^ 2 ≤ seg0_4_0.b := by
  decide +kernel

theorem check_q8_3 :
    ratioCheckI (toInt 156 (qE (-1 / 8) seg0_4_1 qR8 qS8)) (toInt 76 (qW seg0_4_1 qS8)) 156 76 68 18 (-5) (5) 3 12 = true ∧
      isScaled 156 (qE (-1 / 8) seg0_4_1 qR8 qS8) = true ∧ isScaled 76 (qW seg0_4_1 qS8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 45 / 2 ^ 2 - seg0_4_1.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 25 / 2 ^ 1 - seg0_4_1.c ∧
      0 < (45 / 2 ^ 2 : ℚ) ∧ seg0_4_1.a ≤ 45 / 2 ^ 2 ∧ 25 / 2 ^ 1 ≤ seg0_4_1.b := by
  decide +kernel

theorem check_q8_4 :
    ratioCheckI (toInt 156 (qE (-1 / 8) seg0_4_2 qR8 qS8)) (toInt 76 (qW seg0_4_2 qS8)) 156 76 68 18 (-5) (5) 3 12 = true ∧
      isScaled 156 (qE (-1 / 8) seg0_4_2 qR8 qS8) = true ∧ isScaled 76 (qW seg0_4_2 qS8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 25 / 2 ^ 1 - seg0_4_2.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 55 / 2 ^ 2 - seg0_4_2.c ∧
      0 < (25 / 2 ^ 1 : ℚ) ∧ seg0_4_2.a ≤ 25 / 2 ^ 1 ∧ 55 / 2 ^ 2 ≤ seg0_4_2.b := by
  decide +kernel

theorem check_q8_5 :
    ratioCheckI (toInt 156 (qE (-1 / 8) seg0_4_3 qR8 qS8)) (toInt 76 (qW seg0_4_3 qS8)) 156 76 68 18 (-5) (5) 3 12 = true ∧
      isScaled 156 (qE (-1 / 8) seg0_4_3 qR8 qS8) = true ∧ isScaled 76 (qW seg0_4_3 qS8) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 3 = 55 / 2 ^ 2 - seg0_4_3.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 3 = 15 - seg0_4_3.c ∧
      0 < (55 / 2 ^ 2 : ℚ) ∧ seg0_4_3.a ≤ 55 / 2 ^ 2 ∧ 15 ≤ seg0_4_3.b := by
  decide +kernel

theorem check_q8_6 :
    ratioCheckI (toInt 156 (qE (-1 / 8) seg0_5_0 qR8 qS8)) (toInt 76 (qW seg0_5_0 qS8)) 156 76 68 18 (-7) (7) 3 12 = true ∧
      isScaled 156 (qE (-1 / 8) seg0_5_0 qR8 qS8) = true ∧ isScaled 76 (qW seg0_5_0 qS8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 15 - seg0_5_0.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 67 / 2 ^ 2 - seg0_5_0.c ∧
      0 < (15 : ℚ) ∧ seg0_5_0.a ≤ 15 ∧ 67 / 2 ^ 2 ≤ seg0_5_0.b := by
  decide +kernel

theorem check_q8_7 :
    ratioCheckI (toInt 156 (qE (-1 / 8) seg0_5_1 qR8 qS8)) (toInt 76 (qW seg0_5_1 qS8)) 156 76 68 18 (-7) (7) 3 12 = true ∧
      isScaled 156 (qE (-1 / 8) seg0_5_1 qR8 qS8) = true ∧ isScaled 76 (qW seg0_5_1 qS8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 67 / 2 ^ 2 - seg0_5_1.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 37 / 2 ^ 1 - seg0_5_1.c ∧
      0 < (67 / 2 ^ 2 : ℚ) ∧ seg0_5_1.a ≤ 67 / 2 ^ 2 ∧ 37 / 2 ^ 1 ≤ seg0_5_1.b := by
  decide +kernel

theorem check_q8_8 :
    ratioCheckI (toInt 156 (qE (-1 / 8) seg0_5_2 qR8 qS8)) (toInt 76 (qW seg0_5_2 qS8)) 156 76 68 18 (-7) (7) 3 12 = true ∧
      isScaled 156 (qE (-1 / 8) seg0_5_2 qR8 qS8) = true ∧ isScaled 76 (qW seg0_5_2 qS8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 37 / 2 ^ 1 - seg0_5_2.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 81 / 2 ^ 2 - seg0_5_2.c ∧
      0 < (37 / 2 ^ 1 : ℚ) ∧ seg0_5_2.a ≤ 37 / 2 ^ 1 ∧ 81 / 2 ^ 2 ≤ seg0_5_2.b := by
  decide +kernel

theorem check_q8_9 :
    ratioCheckI (toInt 156 (qE (-1 / 8) seg0_5_3 qR8 qS8)) (toInt 76 (qW seg0_5_3 qS8)) 156 76 68 18 (-7) (7) 3 12 = true ∧
      isScaled 156 (qE (-1 / 8) seg0_5_3 qR8 qS8) = true ∧ isScaled 76 (qW seg0_5_3 qS8) = true ∧
      ((-7 : ℤ) : ℚ) / 2 ^ 3 = 81 / 2 ^ 2 - seg0_5_3.c ∧ ((7 : ℤ) : ℚ) / 2 ^ 3 = 22 - seg0_5_3.c ∧
      0 < (81 / 2 ^ 2 : ℚ) ∧ seg0_5_3.a ≤ 81 / 2 ^ 2 ∧ 22 ≤ seg0_5_3.b := by
  decide +kernel

theorem check_q8_10 :
    ratioCheckI (toInt 123 (qE (-1 / 8) seg0_6_0 qR8 qS8)) (toInt 43 (qW seg0_6_0 qS8)) 123 43 68 18 (-1) (1) 0 12 = true ∧
      isScaled 123 (qE (-1 / 8) seg0_6_0 qR8 qS8) = true ∧ isScaled 43 (qW seg0_6_0 qS8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 22 - seg0_6_0.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 24 - seg0_6_0.c ∧
      0 < (22 : ℚ) ∧ seg0_6_0.a ≤ 22 ∧ 24 ≤ seg0_6_0.b := by
  decide +kernel

theorem check_q8_11 :
    ratioCheckI (toInt 123 (qE (-1 / 8) seg0_6_1 qR8 qS8)) (toInt 43 (qW seg0_6_1 qS8)) 123 43 68 18 (-1) (1) 0 12 = true ∧
      isScaled 123 (qE (-1 / 8) seg0_6_1 qR8 qS8) = true ∧ isScaled 43 (qW seg0_6_1 qS8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 24 - seg0_6_1.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 26 - seg0_6_1.c ∧
      0 < (24 : ℚ) ∧ seg0_6_1.a ≤ 24 ∧ 26 ≤ seg0_6_1.b := by
  decide +kernel

theorem check_q8_12 :
    ratioCheckI (toInt 123 (qE (-1 / 8) seg0_6_2 qR8 qS8)) (toInt 43 (qW seg0_6_2 qS8)) 123 43 68 18 (-1) (1) 0 12 = true ∧
      isScaled 123 (qE (-1 / 8) seg0_6_2 qR8 qS8) = true ∧ isScaled 43 (qW seg0_6_2 qS8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 26 - seg0_6_2.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 28 - seg0_6_2.c ∧
      0 < (26 : ℚ) ∧ seg0_6_2.a ≤ 26 ∧ 28 ≤ seg0_6_2.b := by
  decide +kernel

theorem check_q8_13 :
    ratioCheckI (toInt 123 (qE (-1 / 8) seg0_6_3 qR8 qS8)) (toInt 43 (qW seg0_6_3 qS8)) 123 43 68 18 (-1) (1) 0 12 = true ∧
      isScaled 123 (qE (-1 / 8) seg0_6_3 qR8 qS8) = true ∧ isScaled 43 (qW seg0_6_3 qS8) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 0 = 28 - seg0_6_3.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 0 = 30 - seg0_6_3.c ∧
      0 < (28 : ℚ) ∧ seg0_6_3.a ≤ 28 ∧ 30 ≤ seg0_6_3.b := by
  decide +kernel

theorem check_q8_asym :
    ratioCheckI (toInt 77 (qEa (-1 / 8) casym qR8 qS8)) (toInt 43 (sAsym qS8)) 77 43 68 18 0 35 10 12 = true ∧
      isScaled 77 (qEa (-1 / 8) casym qR8 qS8) = true ∧ isScaled 43 (sAsym qS8) = true := by
  decide +kernel

/-- `qzero` on `[8, ∞)`: within `18/2^68 + 2^-70`, about `2 ^ -63.81`. -/
theorem qzero_8 (x : ℝ) (hlo : (((8 : ℚ)) : ℝ) ≤ x) :
    |Q0 x - qFd (-1 / 8) qR8 qS8 x| ≤ 18 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : qR8.length ≤ qS8.length + 1 := by decide
  rcases le_total x (((9 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast q_step (piece0_3, seg0_3_1) (segs_3_ok.2.1) (by simp [pieces, last]) qR8 qS8 hR (8) (9) 134 54 18 _ _ _ ⟨check_q8_0.2.1, check_q8_0.2.2.1⟩ check_q8_0.1 ⟨check_q8_0.2.2.2.1, check_q8_0.2.2.2.2.1⟩ check_q8_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((10 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast q_step (piece0_3, seg0_3_2) (segs_3_ok.2.2) (by simp [pieces, last]) qR8 qS8 hR (9) (10) 134 54 18 _ _ _ ⟨check_q8_1.2.1, check_q8_1.2.2.1⟩ check_q8_1.1 ⟨check_q8_1.2.2.2.1, check_q8_1.2.2.2.2.1⟩ check_q8_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((45 / 2 ^ 2 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast q_step (piece0_4, seg0_4_0) (segs_4_ok.1) (by simp [pieces, last]) qR8 qS8 hR (10) (45 / 2 ^ 2) 156 76 18 _ _ _ ⟨check_q8_2.2.1, check_q8_2.2.2.1⟩ check_q8_2.1 ⟨check_q8_2.2.2.2.1, check_q8_2.2.2.2.2.1⟩ check_q8_2.2.2.2.2.2 x ⟨h1, h2⟩
  rcases le_total x (((25 / 2 ^ 1 : ℚ)) : ℝ) with h3 | h3
  · exact_mod_cast q_step (piece0_4, seg0_4_1) (segs_4_ok.2.1) (by simp [pieces, last]) qR8 qS8 hR (45 / 2 ^ 2) (25 / 2 ^ 1) 156 76 18 _ _ _ ⟨check_q8_3.2.1, check_q8_3.2.2.1⟩ check_q8_3.1 ⟨check_q8_3.2.2.2.1, check_q8_3.2.2.2.2.1⟩ check_q8_3.2.2.2.2.2 x ⟨h2, h3⟩
  rcases le_total x (((55 / 2 ^ 2 : ℚ)) : ℝ) with h4 | h4
  · exact_mod_cast q_step (piece0_4, seg0_4_2) (segs_4_ok.2.2.1) (by simp [pieces, last]) qR8 qS8 hR (25 / 2 ^ 1) (55 / 2 ^ 2) 156 76 18 _ _ _ ⟨check_q8_4.2.1, check_q8_4.2.2.1⟩ check_q8_4.1 ⟨check_q8_4.2.2.2.1, check_q8_4.2.2.2.2.1⟩ check_q8_4.2.2.2.2.2 x ⟨h3, h4⟩
  rcases le_total x (((15 : ℚ)) : ℝ) with h5 | h5
  · exact_mod_cast q_step (piece0_4, seg0_4_3) (segs_4_ok.2.2.2) (by simp [pieces, last]) qR8 qS8 hR (55 / 2 ^ 2) (15) 156 76 18 _ _ _ ⟨check_q8_5.2.1, check_q8_5.2.2.1⟩ check_q8_5.1 ⟨check_q8_5.2.2.2.1, check_q8_5.2.2.2.2.1⟩ check_q8_5.2.2.2.2.2 x ⟨h4, h5⟩
  rcases le_total x (((67 / 2 ^ 2 : ℚ)) : ℝ) with h6 | h6
  · exact_mod_cast q_step (piece0_5, seg0_5_0) (segs_5_ok.1) (by simp [pieces, last]) qR8 qS8 hR (15) (67 / 2 ^ 2) 156 76 18 _ _ _ ⟨check_q8_6.2.1, check_q8_6.2.2.1⟩ check_q8_6.1 ⟨check_q8_6.2.2.2.1, check_q8_6.2.2.2.2.1⟩ check_q8_6.2.2.2.2.2 x ⟨h5, h6⟩
  rcases le_total x (((37 / 2 ^ 1 : ℚ)) : ℝ) with h7 | h7
  · exact_mod_cast q_step (piece0_5, seg0_5_1) (segs_5_ok.2.1) (by simp [pieces, last]) qR8 qS8 hR (67 / 2 ^ 2) (37 / 2 ^ 1) 156 76 18 _ _ _ ⟨check_q8_7.2.1, check_q8_7.2.2.1⟩ check_q8_7.1 ⟨check_q8_7.2.2.2.1, check_q8_7.2.2.2.2.1⟩ check_q8_7.2.2.2.2.2 x ⟨h6, h7⟩
  rcases le_total x (((81 / 2 ^ 2 : ℚ)) : ℝ) with h8 | h8
  · exact_mod_cast q_step (piece0_5, seg0_5_2) (segs_5_ok.2.2.1) (by simp [pieces, last]) qR8 qS8 hR (37 / 2 ^ 1) (81 / 2 ^ 2) 156 76 18 _ _ _ ⟨check_q8_8.2.1, check_q8_8.2.2.1⟩ check_q8_8.1 ⟨check_q8_8.2.2.2.1, check_q8_8.2.2.2.2.1⟩ check_q8_8.2.2.2.2.2 x ⟨h7, h8⟩
  rcases le_total x (((22 : ℚ)) : ℝ) with h9 | h9
  · exact_mod_cast q_step (piece0_5, seg0_5_3) (segs_5_ok.2.2.2) (by simp [pieces, last]) qR8 qS8 hR (81 / 2 ^ 2) (22) 156 76 18 _ _ _ ⟨check_q8_9.2.1, check_q8_9.2.2.1⟩ check_q8_9.1 ⟨check_q8_9.2.2.2.1, check_q8_9.2.2.2.2.1⟩ check_q8_9.2.2.2.2.2 x ⟨h8, h9⟩
  rcases le_total x (((24 : ℚ)) : ℝ) with h10 | h10
  · exact_mod_cast q_step (piece0_6, seg0_6_0) (segs_6_ok.1) (by simp [pieces, last]) qR8 qS8 hR (22) (24) 123 43 18 _ _ _ ⟨check_q8_10.2.1, check_q8_10.2.2.1⟩ check_q8_10.1 ⟨check_q8_10.2.2.2.1, check_q8_10.2.2.2.2.1⟩ check_q8_10.2.2.2.2.2 x ⟨h9, h10⟩
  rcases le_total x (((26 : ℚ)) : ℝ) with h11 | h11
  · exact_mod_cast q_step (piece0_6, seg0_6_1) (segs_6_ok.2.1) (by simp [pieces, last]) qR8 qS8 hR (24) (26) 123 43 18 _ _ _ ⟨check_q8_11.2.1, check_q8_11.2.2.1⟩ check_q8_11.1 ⟨check_q8_11.2.2.2.1, check_q8_11.2.2.2.2.1⟩ check_q8_11.2.2.2.2.2 x ⟨h10, h11⟩
  rcases le_total x (((28 : ℚ)) : ℝ) with h12 | h12
  · exact_mod_cast q_step (piece0_6, seg0_6_2) (segs_6_ok.2.2.1) (by simp [pieces, last]) qR8 qS8 hR (26) (28) 123 43 18 _ _ _ ⟨check_q8_12.2.1, check_q8_12.2.2.1⟩ check_q8_12.1 ⟨check_q8_12.2.2.2.1, check_q8_12.2.2.2.2.1⟩ check_q8_12.2.2.2.2.2 x ⟨h11, h12⟩
  rcases le_total x (((30 : ℚ)) : ℝ) with h13 | h13
  · exact_mod_cast q_step (piece0_6, seg0_6_3) (segs_6_ok.2.2.2) (by simp [pieces, last]) qR8 qS8 hR (28) (30) 123 43 18 _ _ _ ⟨check_q8_13.2.1, check_q8_13.2.2.1⟩ check_q8_13.1 ⟨check_q8_13.2.2.2.1, check_q8_13.2.2.2.2.1⟩ check_q8_13.2.2.2.2.2 x ⟨h12, h13⟩
  exact_mod_cast q_asym_step qR8 qS8 77 43 18 check_q8_asym.2 check_q8_asym.1 x (by exact_mod_cast h13)

#print axioms pzero_8
#print axioms qzero_8

end LeanExe.ProofKit.BesselFd0b
