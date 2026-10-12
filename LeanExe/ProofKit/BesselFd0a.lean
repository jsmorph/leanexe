import LeanExe.ProofKit.BesselSeg0

/-!
fdlibm's rational approximations `pzero` and `qzero` of `P0` and `Q0` from `e_j0.c` (FreeBSD msun
at commit `20381bce4b63975494a2f4bc84257f6932e6d379`) on the ranges that start at
`2`, `b3`, `b5`, where `b3 = 0x4006DB6D00000000` (about 2.8571) and
`b5 = 0x40122E8B00000000` (about 4.5454) are the boundaries that `e_j0.c` tests on the high word.
`pFd R S x` and `qFd (-1/8) R S x` are fdlibm's formulas without rounding, with the coefficient lists
`ratOfWord` of the words that `e_j0.c` gives beside the decimal values.  Each theorem bounds
`|P0 x - pFd R S x|` or `|Q0 x - qFd (-1/8) R S x|` for every real `x` in the range, from one
kernel check (`ratioCheckI`) per segment of `BesselSeg0` and, from 30 on, per Hankel's expansion.
-/

namespace LeanExe.ProofKit.BesselFd0a

open Set PolyBound PolyCalc BesselPQ BesselChain BesselRatio BesselLarge0 BesselSeg0

/-- The boundary `0x4006DB6D00000000` of fdlibm's ranges. -/
def b3 : ℚ := ratOfWord 0x4006DB6D00000000

/-- The boundary `0x40122E8B00000000` of fdlibm's ranges. -/
def b5 : ℚ := ratOfWord 0x40122E8B00000000

/-- `pR2` of `e_j0.c`. -/
def pR2 : List ℚ := [ratOfWord 0xBE77D316E927026D, ratOfWord 0xBFB1FF62495E1E42, ratOfWord 0xBFF736398A24A843, ratOfWord 0xC01E8AF3EDAFA7F3, ratOfWord 0xC02662E6C5246303, ratOfWord 0xC009DE81AF8FE70F]
/-- `pS2` of `e_j0.c`. -/
def pS2 : List ℚ := [ratOfWord 0x40363865908B5959, ratOfWord 0x4061069E0EE8878F, ratOfWord 0x4070E78642EA079B, ratOfWord 0x40633C033AB6FAFF, ratOfWord 0x402D50B344391809]

/-- `qR2` of `e_j0.c`. -/
def qR2 : List ℚ := [ratOfWord 0x3E84313B54F76BDB, ratOfWord 0x3FB2BEC53E883E34, ratOfWord 0x3FFFF897E727779C, ratOfWord 0x402CFDBFAAF96FE5, ratOfWord 0x403FAA8E29FBDC4A, ratOfWord 0x403040B171814BB4]
/-- `qS2` of `e_j0.c`. -/
def qS2 : List ℚ := [ratOfWord 0x403E5D96F7C07AED, ratOfWord 0x4070D591E4D14B40, ratOfWord 0x408A664522B3BF22, ratOfWord 0x408B977C9C5CC214, ratOfWord 0x406A95530E001365, ratOfWord 0xC0153E6AF8B32931]

/-- `pR3` of `e_j0.c`. -/
def pR3 : List ℚ := [ratOfWord 0xBE25E1036FE1AA86, ratOfWord 0xBFB1FFF6F7C0E24B, ratOfWord 0xC00345B2AEA48074, ratOfWord 0xC035F74A4CB94E14, ratOfWord 0xC04D0A22420A1A45, ratOfWord 0xC03F72ACA892D80F]
/-- `pS3` of `e_j0.c`. -/
def pS3 : List ℚ := [ratOfWord 0x4041ED9284077DD3, ratOfWord 0x40769839464A7C0E, ratOfWord 0x4092A66E6D1061D6, ratOfWord 0x40919FFCB8C39B7E, ratOfWord 0x4065B296FC379081]

/-- `qR3` of `e_j0.c`. -/
def qR3 : List ℚ := [ratOfWord 0x3E32CD036ADECB82, ratOfWord 0x3FB2BFEE0E8D0842, ratOfWord 0x400AC0FC61149CF5, ratOfWord 0x40454F98962DAEDD, ratOfWord 0x406559DBE25EFD1F, ratOfWord 0x4064D77C81FA21E0]
/-- `qS3` of `e_j0.c`. -/
def qS3 : List ℚ := [ratOfWord 0x40486122BFE343A6, ratOfWord 0x40862D8386544EB3, ratOfWord 0x40ACF04BE44DFC63, ratOfWord 0x40B93C6CD7C76A28, ratOfWord 0x40A3A8AAD94FB1C0, ratOfWord 0xC062A7EB201CF40F]

/-- `pR5` of `e_j0.c`. -/
def pR5 : List ℚ := [ratOfWord 0xBDA918B147E495CC, ratOfWord 0xBFB1FFFFE69AFBC6, ratOfWord 0xC010A370F90C6BBF, ratOfWord 0xC050EB2F5A7D1783, ratOfWord 0xC074B3B36742CC63, ratOfWord 0xC075A6EF28A38BD7]
/-- `pS5` of `e_j0.c`. -/
def pS5 : List ℚ := [ratOfWord 0x404E60810C98C5DE, ratOfWord 0x40906D025C7E2864, ratOfWord 0x40B75AF88FBE1D60, ratOfWord 0x40C2CCB8FA76FA38, ratOfWord 0x40A2CC1DC70BE864]

/-- `qR5` of `e_j0.c`. -/
def qR5 : List ℚ := [ratOfWord 0x3DB43D8F29CC8CD9, ratOfWord 0x3FB2BFFFD172B04C, ratOfWord 0x401757B0B9953DD3, ratOfWord 0x4060E3920A8788E9, ratOfWord 0x40900CF99DC8C481, ratOfWord 0x409F17E953C6E3A6]
/-- `qS5` of `e_j0.c`. -/
def qS5 : List ℚ := [ratOfWord 0x4054B1B3FB5E1543, ratOfWord 0x40A03BA0DA21C0CE, ratOfWord 0x40D267D27B591E6D, ratOfWord 0x40EBB5E397E02372, ratOfWord 0x40E191181F7A54A0, ratOfWord 0xC0B4EA57BEDBC609]

theorem check_p2_0 :
    ratioCheckI (toInt 152 (pE seg0_0_0 pR2 pS2)) (toInt 72 (sTilde seg0_0_0.c pS2)) 152 72 68 1067 (-1) (1) 3 12 = true ∧
      isScaled 152 (pE seg0_0_0 pR2 pS2) = true ∧ isScaled 72 (sTilde seg0_0_0.c pS2) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 3 = 2 - seg0_0_0.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 3 = 9 / 2 ^ 2 - seg0_0_0.c ∧
      0 < (2 : ℚ) ∧ seg0_0_0.a ≤ 2 ∧ 9 / 2 ^ 2 ≤ seg0_0_0.b := by
  decide +kernel

theorem check_p2_1 :
    ratioCheckI (toInt 152 (pE seg0_0_1 pR2 pS2)) (toInt 72 (sTilde seg0_0_1.c pS2)) 152 72 68 1067 (-1) (1) 3 12 = true ∧
      isScaled 152 (pE seg0_0_1 pR2 pS2) = true ∧ isScaled 72 (sTilde seg0_0_1.c pS2) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 3 = 9 / 2 ^ 2 - seg0_0_1.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 3 = 5 / 2 ^ 1 - seg0_0_1.c ∧
      0 < (9 / 2 ^ 2 : ℚ) ∧ seg0_0_1.a ≤ 9 / 2 ^ 2 ∧ 5 / 2 ^ 1 ≤ seg0_0_1.b := by
  decide +kernel

theorem check_p2_2 :
    ratioCheckI (toInt 152 (pE seg0_0_2 pR2 pS2)) (toInt 72 (sTilde seg0_0_2.c pS2)) 152 72 68 1067 (-1) (1) 3 12 = true ∧
      isScaled 152 (pE seg0_0_2 pR2 pS2) = true ∧ isScaled 72 (sTilde seg0_0_2.c pS2) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 3 = 5 / 2 ^ 1 - seg0_0_2.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 3 = 11 / 2 ^ 2 - seg0_0_2.c ∧
      0 < (5 / 2 ^ 1 : ℚ) ∧ seg0_0_2.a ≤ 5 / 2 ^ 1 ∧ 11 / 2 ^ 2 ≤ seg0_0_2.b := by
  decide +kernel

theorem check_p2_3 :
    ratioCheckI (toInt 152 (pE seg0_0_3 pR2 pS2)) (toInt 72 (sTilde seg0_0_3.c pS2)) 152 72 68 1067 (-65536) (-9363) 19 12 = true ∧
      isScaled 152 (pE seg0_0_3 pR2 pS2) = true ∧ isScaled 72 (sTilde seg0_0_3.c pS2) = true ∧
      ((-65536 : ℤ) : ℚ) / 2 ^ 19 = 11 / 2 ^ 2 - seg0_0_3.c ∧ ((-9363 : ℤ) : ℚ) / 2 ^ 19 = b3 - seg0_0_3.c ∧
      0 < (11 / 2 ^ 2 : ℚ) ∧ seg0_0_3.a ≤ 11 / 2 ^ 2 ∧ b3 ≤ seg0_0_3.b := by
  decide +kernel

/-- `pzero` on `[2, b3]`: within `1067/2^68 + 2^-70`, about `2 ^ -57.94`. -/
theorem pzero_2 (x : ℝ) (hlo : (((2 : ℚ)) : ℝ) ≤ x) (hhi : x ≤ (((b3 : ℚ)) : ℝ)) :
    |P0 x - pFd pR2 pS2 x| ≤ 1067 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : pR2.length ≤ pS2.length + 1 := by decide
  rcases le_total x (((9 / 2 ^ 2 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast p_step (piece0_0, seg0_0_0) (segs_0_ok.1) (by simp [pieces, last]) pR2 pS2 hR (2) (9 / 2 ^ 2) 152 72 1067 _ _ _ ⟨check_p2_0.2.1, check_p2_0.2.2.1⟩ check_p2_0.1 ⟨check_p2_0.2.2.2.1, check_p2_0.2.2.2.2.1⟩ check_p2_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((5 / 2 ^ 1 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast p_step (piece0_0, seg0_0_1) (segs_0_ok.2.1) (by simp [pieces, last]) pR2 pS2 hR (9 / 2 ^ 2) (5 / 2 ^ 1) 152 72 1067 _ _ _ ⟨check_p2_1.2.1, check_p2_1.2.2.1⟩ check_p2_1.1 ⟨check_p2_1.2.2.2.1, check_p2_1.2.2.2.2.1⟩ check_p2_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((11 / 2 ^ 2 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast p_step (piece0_0, seg0_0_2) (segs_0_ok.2.2.1) (by simp [pieces, last]) pR2 pS2 hR (5 / 2 ^ 1) (11 / 2 ^ 2) 152 72 1067 _ _ _ ⟨check_p2_2.2.1, check_p2_2.2.2.1⟩ check_p2_2.1 ⟨check_p2_2.2.2.2.1, check_p2_2.2.2.2.2.1⟩ check_p2_2.2.2.2.2.2 x ⟨h1, h2⟩
  exact_mod_cast p_step (piece0_0, seg0_0_3) (segs_0_ok.2.2.2) (by simp [pieces, last]) pR2 pS2 hR (11 / 2 ^ 2) (b3) 152 72 1067 _ _ _ ⟨check_p2_3.2.1, check_p2_3.2.2.1⟩ check_p2_3.1 ⟨check_p2_3.2.2.2.1, check_p2_3.2.2.2.2.1⟩ check_p2_3.2.2.2.2.2 x ⟨h2, hhi⟩

theorem check_q2_0 :
    ratioCheckI (toInt 161 (qE (-1 / 8) seg0_0_0 qR2 qS2)) (toInt 81 (qW seg0_0_0 qS2)) 161 81 68 127 (-1) (1) 3 12 = true ∧
      isScaled 161 (qE (-1 / 8) seg0_0_0 qR2 qS2) = true ∧ isScaled 81 (qW seg0_0_0 qS2) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 3 = 2 - seg0_0_0.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 3 = 9 / 2 ^ 2 - seg0_0_0.c ∧
      0 < (2 : ℚ) ∧ seg0_0_0.a ≤ 2 ∧ 9 / 2 ^ 2 ≤ seg0_0_0.b := by
  decide +kernel

theorem check_q2_1 :
    ratioCheckI (toInt 161 (qE (-1 / 8) seg0_0_1 qR2 qS2)) (toInt 81 (qW seg0_0_1 qS2)) 161 81 68 127 (-1) (1) 3 12 = true ∧
      isScaled 161 (qE (-1 / 8) seg0_0_1 qR2 qS2) = true ∧ isScaled 81 (qW seg0_0_1 qS2) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 3 = 9 / 2 ^ 2 - seg0_0_1.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 3 = 5 / 2 ^ 1 - seg0_0_1.c ∧
      0 < (9 / 2 ^ 2 : ℚ) ∧ seg0_0_1.a ≤ 9 / 2 ^ 2 ∧ 5 / 2 ^ 1 ≤ seg0_0_1.b := by
  decide +kernel

theorem check_q2_2 :
    ratioCheckI (toInt 161 (qE (-1 / 8) seg0_0_2 qR2 qS2)) (toInt 81 (qW seg0_0_2 qS2)) 161 81 68 127 (-1) (1) 3 12 = true ∧
      isScaled 161 (qE (-1 / 8) seg0_0_2 qR2 qS2) = true ∧ isScaled 81 (qW seg0_0_2 qS2) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 3 = 5 / 2 ^ 1 - seg0_0_2.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 3 = 11 / 2 ^ 2 - seg0_0_2.c ∧
      0 < (5 / 2 ^ 1 : ℚ) ∧ seg0_0_2.a ≤ 5 / 2 ^ 1 ∧ 11 / 2 ^ 2 ≤ seg0_0_2.b := by
  decide +kernel

theorem check_q2_3 :
    ratioCheckI (toInt 161 (qE (-1 / 8) seg0_0_3 qR2 qS2)) (toInt 81 (qW seg0_0_3 qS2)) 161 81 68 127 (-65536) (-9363) 19 12 = true ∧
      isScaled 161 (qE (-1 / 8) seg0_0_3 qR2 qS2) = true ∧ isScaled 81 (qW seg0_0_3 qS2) = true ∧
      ((-65536 : ℤ) : ℚ) / 2 ^ 19 = 11 / 2 ^ 2 - seg0_0_3.c ∧ ((-9363 : ℤ) : ℚ) / 2 ^ 19 = b3 - seg0_0_3.c ∧
      0 < (11 / 2 ^ 2 : ℚ) ∧ seg0_0_3.a ≤ 11 / 2 ^ 2 ∧ b3 ≤ seg0_0_3.b := by
  decide +kernel

/-- `qzero` on `[2, b3]`: within `127/2^68 + 2^-70`, about `2 ^ -61.01`. -/
theorem qzero_2 (x : ℝ) (hlo : (((2 : ℚ)) : ℝ) ≤ x) (hhi : x ≤ (((b3 : ℚ)) : ℝ)) :
    |Q0 x - qFd (-1 / 8) qR2 qS2 x| ≤ 127 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : qR2.length ≤ qS2.length + 1 := by decide
  rcases le_total x (((9 / 2 ^ 2 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast q_step (piece0_0, seg0_0_0) (segs_0_ok.1) (by simp [pieces, last]) qR2 qS2 hR (2) (9 / 2 ^ 2) 161 81 127 _ _ _ ⟨check_q2_0.2.1, check_q2_0.2.2.1⟩ check_q2_0.1 ⟨check_q2_0.2.2.2.1, check_q2_0.2.2.2.2.1⟩ check_q2_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((5 / 2 ^ 1 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast q_step (piece0_0, seg0_0_1) (segs_0_ok.2.1) (by simp [pieces, last]) qR2 qS2 hR (9 / 2 ^ 2) (5 / 2 ^ 1) 161 81 127 _ _ _ ⟨check_q2_1.2.1, check_q2_1.2.2.1⟩ check_q2_1.1 ⟨check_q2_1.2.2.2.1, check_q2_1.2.2.2.2.1⟩ check_q2_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((11 / 2 ^ 2 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast q_step (piece0_0, seg0_0_2) (segs_0_ok.2.2.1) (by simp [pieces, last]) qR2 qS2 hR (5 / 2 ^ 1) (11 / 2 ^ 2) 161 81 127 _ _ _ ⟨check_q2_2.2.1, check_q2_2.2.2.1⟩ check_q2_2.1 ⟨check_q2_2.2.2.2.1, check_q2_2.2.2.2.2.1⟩ check_q2_2.2.2.2.2.2 x ⟨h1, h2⟩
  exact_mod_cast q_step (piece0_0, seg0_0_3) (segs_0_ok.2.2.2) (by simp [pieces, last]) qR2 qS2 hR (11 / 2 ^ 2) (b3) 161 81 127 _ _ _ ⟨check_q2_3.2.1, check_q2_3.2.2.1⟩ check_q2_3.1 ⟨check_q2_3.2.2.2.1, check_q2_3.2.2.2.2.1⟩ check_q2_3.2.2.2.2.2 x ⟨h2, hhi⟩

theorem check_p3_0 :
    ratioCheckI (toInt 151 (pE seg0_0_3 pR3 pS3)) (toInt 71 (sTilde seg0_0_3.c pS3)) 151 71 68 1662 (-9363) (65536) 19 12 = true ∧
      isScaled 151 (pE seg0_0_3 pR3 pS3) = true ∧ isScaled 71 (sTilde seg0_0_3.c pS3) = true ∧
      ((-9363 : ℤ) : ℚ) / 2 ^ 19 = b3 - seg0_0_3.c ∧ ((65536 : ℤ) : ℚ) / 2 ^ 19 = 3 - seg0_0_3.c ∧
      0 < (b3 : ℚ) ∧ seg0_0_3.a ≤ b3 ∧ 3 ≤ seg0_0_3.b := by
  decide +kernel

theorem check_p3_1 :
    ratioCheckI (toInt 159 (pE seg0_1_0 pR3 pS3)) (toInt 79 (sTilde seg0_1_0.c pS3)) 159 79 68 1662 (-3) (3) 4 12 = true ∧
      isScaled 159 (pE seg0_1_0 pR3 pS3) = true ∧ isScaled 79 (sTilde seg0_1_0.c pS3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 3 - seg0_1_0.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 27 / 2 ^ 3 - seg0_1_0.c ∧
      0 < (3 : ℚ) ∧ seg0_1_0.a ≤ 3 ∧ 27 / 2 ^ 3 ≤ seg0_1_0.b := by
  decide +kernel

theorem check_p3_2 :
    ratioCheckI (toInt 159 (pE seg0_1_1 pR3 pS3)) (toInt 79 (sTilde seg0_1_1.c pS3)) 159 79 68 1662 (-3) (3) 4 12 = true ∧
      isScaled 159 (pE seg0_1_1 pR3 pS3) = true ∧ isScaled 79 (sTilde seg0_1_1.c pS3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 27 / 2 ^ 3 - seg0_1_1.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 15 / 2 ^ 2 - seg0_1_1.c ∧
      0 < (27 / 2 ^ 3 : ℚ) ∧ seg0_1_1.a ≤ 27 / 2 ^ 3 ∧ 15 / 2 ^ 2 ≤ seg0_1_1.b := by
  decide +kernel

theorem check_p3_3 :
    ratioCheckI (toInt 159 (pE seg0_1_2 pR3 pS3)) (toInt 79 (sTilde seg0_1_2.c pS3)) 159 79 68 1662 (-3) (3) 4 12 = true ∧
      isScaled 159 (pE seg0_1_2 pR3 pS3) = true ∧ isScaled 79 (sTilde seg0_1_2.c pS3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 15 / 2 ^ 2 - seg0_1_2.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 33 / 2 ^ 3 - seg0_1_2.c ∧
      0 < (15 / 2 ^ 2 : ℚ) ∧ seg0_1_2.a ≤ 15 / 2 ^ 2 ∧ 33 / 2 ^ 3 ≤ seg0_1_2.b := by
  decide +kernel

theorem check_p3_4 :
    ratioCheckI (toInt 159 (pE seg0_1_3 pR3 pS3)) (toInt 79 (sTilde seg0_1_3.c pS3)) 159 79 68 1662 (-3) (3) 4 12 = true ∧
      isScaled 159 (pE seg0_1_3 pR3 pS3) = true ∧ isScaled 79 (sTilde seg0_1_3.c pS3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 33 / 2 ^ 3 - seg0_1_3.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 9 / 2 ^ 1 - seg0_1_3.c ∧
      0 < (33 / 2 ^ 3 : ℚ) ∧ seg0_1_3.a ≤ 33 / 2 ^ 3 ∧ 9 / 2 ^ 1 ≤ seg0_1_3.b := by
  decide +kernel

theorem check_p3_5 :
    ratioCheckI (toInt 159 (pE seg0_2_0 pR3 pS3)) (toInt 79 (sTilde seg0_2_0.c pS3)) 159 79 68 1662 (-81920) (-70005) 18 12 = true ∧
      isScaled 159 (pE seg0_2_0 pR3 pS3) = true ∧ isScaled 79 (sTilde seg0_2_0.c pS3) = true ∧
      ((-81920 : ℤ) : ℚ) / 2 ^ 18 = 9 / 2 ^ 1 - seg0_2_0.c ∧ ((-70005 : ℤ) : ℚ) / 2 ^ 18 = b5 - seg0_2_0.c ∧
      0 < (9 / 2 ^ 1 : ℚ) ∧ seg0_2_0.a ≤ 9 / 2 ^ 1 ∧ b5 ≤ seg0_2_0.b := by
  decide +kernel

/-- `pzero` on `[b3, b5]`: within `1662/2^68 + 2^-70`, about `2 ^ -57.30`. -/
theorem pzero_3 (x : ℝ) (hlo : (((b3 : ℚ)) : ℝ) ≤ x) (hhi : x ≤ (((b5 : ℚ)) : ℝ)) :
    |P0 x - pFd pR3 pS3 x| ≤ 1662 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : pR3.length ≤ pS3.length + 1 := by decide
  rcases le_total x (((3 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast p_step (piece0_0, seg0_0_3) (segs_0_ok.2.2.2) (by simp [pieces, last]) pR3 pS3 hR (b3) (3) 151 71 1662 _ _ _ ⟨check_p3_0.2.1, check_p3_0.2.2.1⟩ check_p3_0.1 ⟨check_p3_0.2.2.2.1, check_p3_0.2.2.2.2.1⟩ check_p3_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((27 / 2 ^ 3 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast p_step (piece0_1, seg0_1_0) (segs_1_ok.1) (by simp [pieces, last]) pR3 pS3 hR (3) (27 / 2 ^ 3) 159 79 1662 _ _ _ ⟨check_p3_1.2.1, check_p3_1.2.2.1⟩ check_p3_1.1 ⟨check_p3_1.2.2.2.1, check_p3_1.2.2.2.2.1⟩ check_p3_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((15 / 2 ^ 2 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast p_step (piece0_1, seg0_1_1) (segs_1_ok.2.1) (by simp [pieces, last]) pR3 pS3 hR (27 / 2 ^ 3) (15 / 2 ^ 2) 159 79 1662 _ _ _ ⟨check_p3_2.2.1, check_p3_2.2.2.1⟩ check_p3_2.1 ⟨check_p3_2.2.2.2.1, check_p3_2.2.2.2.2.1⟩ check_p3_2.2.2.2.2.2 x ⟨h1, h2⟩
  rcases le_total x (((33 / 2 ^ 3 : ℚ)) : ℝ) with h3 | h3
  · exact_mod_cast p_step (piece0_1, seg0_1_2) (segs_1_ok.2.2.1) (by simp [pieces, last]) pR3 pS3 hR (15 / 2 ^ 2) (33 / 2 ^ 3) 159 79 1662 _ _ _ ⟨check_p3_3.2.1, check_p3_3.2.2.1⟩ check_p3_3.1 ⟨check_p3_3.2.2.2.1, check_p3_3.2.2.2.2.1⟩ check_p3_3.2.2.2.2.2 x ⟨h2, h3⟩
  rcases le_total x (((9 / 2 ^ 1 : ℚ)) : ℝ) with h4 | h4
  · exact_mod_cast p_step (piece0_1, seg0_1_3) (segs_1_ok.2.2.2) (by simp [pieces, last]) pR3 pS3 hR (33 / 2 ^ 3) (9 / 2 ^ 1) 159 79 1662 _ _ _ ⟨check_p3_4.2.1, check_p3_4.2.2.1⟩ check_p3_4.1 ⟨check_p3_4.2.2.2.1, check_p3_4.2.2.2.2.1⟩ check_p3_4.2.2.2.2.2 x ⟨h3, h4⟩
  exact_mod_cast p_step (piece0_2, seg0_2_0) (segs_2_ok.1) (by simp [pieces, last]) pR3 pS3 hR (9 / 2 ^ 1) (b5) 159 79 1662 _ _ _ ⟨check_p3_5.2.1, check_p3_5.2.2.1⟩ check_p3_5.1 ⟨check_p3_5.2.2.2.1, check_p3_5.2.2.2.2.1⟩ check_p3_5.2.2.2.2.2 x ⟨h4, hhi⟩

theorem check_q3_0 :
    ratioCheckI (toInt 159 (qE (-1 / 8) seg0_0_3 qR3 qS3)) (toInt 79 (qW seg0_0_3 qS3)) 159 79 68 109 (-9363) (65536) 19 12 = true ∧
      isScaled 159 (qE (-1 / 8) seg0_0_3 qR3 qS3) = true ∧ isScaled 79 (qW seg0_0_3 qS3) = true ∧
      ((-9363 : ℤ) : ℚ) / 2 ^ 19 = b3 - seg0_0_3.c ∧ ((65536 : ℤ) : ℚ) / 2 ^ 19 = 3 - seg0_0_3.c ∧
      0 < (b3 : ℚ) ∧ seg0_0_3.a ≤ b3 ∧ 3 ≤ seg0_0_3.b := by
  decide +kernel

theorem check_q3_1 :
    ratioCheckI (toInt 170 (qE (-1 / 8) seg0_1_0 qR3 qS3)) (toInt 90 (qW seg0_1_0 qS3)) 170 90 68 109 (-3) (3) 4 12 = true ∧
      isScaled 170 (qE (-1 / 8) seg0_1_0 qR3 qS3) = true ∧ isScaled 90 (qW seg0_1_0 qS3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 3 - seg0_1_0.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 27 / 2 ^ 3 - seg0_1_0.c ∧
      0 < (3 : ℚ) ∧ seg0_1_0.a ≤ 3 ∧ 27 / 2 ^ 3 ≤ seg0_1_0.b := by
  decide +kernel

theorem check_q3_2 :
    ratioCheckI (toInt 170 (qE (-1 / 8) seg0_1_1 qR3 qS3)) (toInt 90 (qW seg0_1_1 qS3)) 170 90 68 109 (-3) (3) 4 12 = true ∧
      isScaled 170 (qE (-1 / 8) seg0_1_1 qR3 qS3) = true ∧ isScaled 90 (qW seg0_1_1 qS3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 27 / 2 ^ 3 - seg0_1_1.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 15 / 2 ^ 2 - seg0_1_1.c ∧
      0 < (27 / 2 ^ 3 : ℚ) ∧ seg0_1_1.a ≤ 27 / 2 ^ 3 ∧ 15 / 2 ^ 2 ≤ seg0_1_1.b := by
  decide +kernel

theorem check_q3_3 :
    ratioCheckI (toInt 170 (qE (-1 / 8) seg0_1_2 qR3 qS3)) (toInt 90 (qW seg0_1_2 qS3)) 170 90 68 109 (-3) (3) 4 12 = true ∧
      isScaled 170 (qE (-1 / 8) seg0_1_2 qR3 qS3) = true ∧ isScaled 90 (qW seg0_1_2 qS3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 15 / 2 ^ 2 - seg0_1_2.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 33 / 2 ^ 3 - seg0_1_2.c ∧
      0 < (15 / 2 ^ 2 : ℚ) ∧ seg0_1_2.a ≤ 15 / 2 ^ 2 ∧ 33 / 2 ^ 3 ≤ seg0_1_2.b := by
  decide +kernel

theorem check_q3_4 :
    ratioCheckI (toInt 170 (qE (-1 / 8) seg0_1_3 qR3 qS3)) (toInt 90 (qW seg0_1_3 qS3)) 170 90 68 109 (-3) (3) 4 12 = true ∧
      isScaled 170 (qE (-1 / 8) seg0_1_3 qR3 qS3) = true ∧ isScaled 90 (qW seg0_1_3 qS3) = true ∧
      ((-3 : ℤ) : ℚ) / 2 ^ 4 = 33 / 2 ^ 3 - seg0_1_3.c ∧ ((3 : ℤ) : ℚ) / 2 ^ 4 = 9 / 2 ^ 1 - seg0_1_3.c ∧
      0 < (33 / 2 ^ 3 : ℚ) ∧ seg0_1_3.a ≤ 33 / 2 ^ 3 ∧ 9 / 2 ^ 1 ≤ seg0_1_3.b := by
  decide +kernel

theorem check_q3_5 :
    ratioCheckI (toInt 170 (qE (-1 / 8) seg0_2_0 qR3 qS3)) (toInt 90 (qW seg0_2_0 qS3)) 170 90 68 109 (-81920) (-70005) 18 12 = true ∧
      isScaled 170 (qE (-1 / 8) seg0_2_0 qR3 qS3) = true ∧ isScaled 90 (qW seg0_2_0 qS3) = true ∧
      ((-81920 : ℤ) : ℚ) / 2 ^ 18 = 9 / 2 ^ 1 - seg0_2_0.c ∧ ((-70005 : ℤ) : ℚ) / 2 ^ 18 = b5 - seg0_2_0.c ∧
      0 < (9 / 2 ^ 1 : ℚ) ∧ seg0_2_0.a ≤ 9 / 2 ^ 1 ∧ b5 ≤ seg0_2_0.b := by
  decide +kernel

/-- `qzero` on `[b3, b5]`: within `109/2^68 + 2^-70`, about `2 ^ -61.23`. -/
theorem qzero_3 (x : ℝ) (hlo : (((b3 : ℚ)) : ℝ) ≤ x) (hhi : x ≤ (((b5 : ℚ)) : ℝ)) :
    |Q0 x - qFd (-1 / 8) qR3 qS3 x| ≤ 109 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : qR3.length ≤ qS3.length + 1 := by decide
  rcases le_total x (((3 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast q_step (piece0_0, seg0_0_3) (segs_0_ok.2.2.2) (by simp [pieces, last]) qR3 qS3 hR (b3) (3) 159 79 109 _ _ _ ⟨check_q3_0.2.1, check_q3_0.2.2.1⟩ check_q3_0.1 ⟨check_q3_0.2.2.2.1, check_q3_0.2.2.2.2.1⟩ check_q3_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((27 / 2 ^ 3 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast q_step (piece0_1, seg0_1_0) (segs_1_ok.1) (by simp [pieces, last]) qR3 qS3 hR (3) (27 / 2 ^ 3) 170 90 109 _ _ _ ⟨check_q3_1.2.1, check_q3_1.2.2.1⟩ check_q3_1.1 ⟨check_q3_1.2.2.2.1, check_q3_1.2.2.2.2.1⟩ check_q3_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((15 / 2 ^ 2 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast q_step (piece0_1, seg0_1_1) (segs_1_ok.2.1) (by simp [pieces, last]) qR3 qS3 hR (27 / 2 ^ 3) (15 / 2 ^ 2) 170 90 109 _ _ _ ⟨check_q3_2.2.1, check_q3_2.2.2.1⟩ check_q3_2.1 ⟨check_q3_2.2.2.2.1, check_q3_2.2.2.2.2.1⟩ check_q3_2.2.2.2.2.2 x ⟨h1, h2⟩
  rcases le_total x (((33 / 2 ^ 3 : ℚ)) : ℝ) with h3 | h3
  · exact_mod_cast q_step (piece0_1, seg0_1_2) (segs_1_ok.2.2.1) (by simp [pieces, last]) qR3 qS3 hR (15 / 2 ^ 2) (33 / 2 ^ 3) 170 90 109 _ _ _ ⟨check_q3_3.2.1, check_q3_3.2.2.1⟩ check_q3_3.1 ⟨check_q3_3.2.2.2.1, check_q3_3.2.2.2.2.1⟩ check_q3_3.2.2.2.2.2 x ⟨h2, h3⟩
  rcases le_total x (((9 / 2 ^ 1 : ℚ)) : ℝ) with h4 | h4
  · exact_mod_cast q_step (piece0_1, seg0_1_3) (segs_1_ok.2.2.2) (by simp [pieces, last]) qR3 qS3 hR (33 / 2 ^ 3) (9 / 2 ^ 1) 170 90 109 _ _ _ ⟨check_q3_4.2.1, check_q3_4.2.2.1⟩ check_q3_4.1 ⟨check_q3_4.2.2.2.1, check_q3_4.2.2.2.2.1⟩ check_q3_4.2.2.2.2.2 x ⟨h3, h4⟩
  exact_mod_cast q_step (piece0_2, seg0_2_0) (segs_2_ok.1) (by simp [pieces, last]) qR3 qS3 hR (9 / 2 ^ 1) (b5) 170 90 109 _ _ _ ⟨check_q3_5.2.1, check_q3_5.2.2.1⟩ check_q3_5.1 ⟨check_q3_5.2.2.2.1, check_q3_5.2.2.2.2.1⟩ check_q3_5.2.2.2.2.2 x ⟨h4, hhi⟩

theorem check_p5_0 :
    ratioCheckI (toInt 158 (pE seg0_2_0 pR5 pS5)) (toInt 78 (sTilde seg0_2_0.c pS5)) 158 78 68 277 (-70005) (81920) 18 12 = true ∧
      isScaled 158 (pE seg0_2_0 pR5 pS5) = true ∧ isScaled 78 (sTilde seg0_2_0.c pS5) = true ∧
      ((-70005 : ℤ) : ℚ) / 2 ^ 18 = b5 - seg0_2_0.c ∧ ((81920 : ℤ) : ℚ) / 2 ^ 18 = 41 / 2 ^ 3 - seg0_2_0.c ∧
      0 < (b5 : ℚ) ∧ seg0_2_0.a ≤ b5 ∧ 41 / 2 ^ 3 ≤ seg0_2_0.b := by
  decide +kernel

theorem check_p5_1 :
    ratioCheckI (toInt 158 (pE seg0_2_1 pR5 pS5)) (toInt 78 (sTilde seg0_2_1.c pS5)) 158 78 68 277 (-5) (5) 4 12 = true ∧
      isScaled 158 (pE seg0_2_1 pR5 pS5) = true ∧ isScaled 78 (sTilde seg0_2_1.c pS5) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 4 = 41 / 2 ^ 3 - seg0_2_1.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 4 = 23 / 2 ^ 2 - seg0_2_1.c ∧
      0 < (41 / 2 ^ 3 : ℚ) ∧ seg0_2_1.a ≤ 41 / 2 ^ 3 ∧ 23 / 2 ^ 2 ≤ seg0_2_1.b := by
  decide +kernel

theorem check_p5_2 :
    ratioCheckI (toInt 158 (pE seg0_2_2 pR5 pS5)) (toInt 78 (sTilde seg0_2_2.c pS5)) 158 78 68 277 (-5) (5) 4 12 = true ∧
      isScaled 158 (pE seg0_2_2 pR5 pS5) = true ∧ isScaled 78 (sTilde seg0_2_2.c pS5) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 4 = 23 / 2 ^ 2 - seg0_2_2.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 4 = 51 / 2 ^ 3 - seg0_2_2.c ∧
      0 < (23 / 2 ^ 2 : ℚ) ∧ seg0_2_2.a ≤ 23 / 2 ^ 2 ∧ 51 / 2 ^ 3 ≤ seg0_2_2.b := by
  decide +kernel

theorem check_p5_3 :
    ratioCheckI (toInt 158 (pE seg0_2_3 pR5 pS5)) (toInt 78 (sTilde seg0_2_3.c pS5)) 158 78 68 277 (-5) (5) 4 12 = true ∧
      isScaled 158 (pE seg0_2_3 pR5 pS5) = true ∧ isScaled 78 (sTilde seg0_2_3.c pS5) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 4 = 51 / 2 ^ 3 - seg0_2_3.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 4 = 7 - seg0_2_3.c ∧
      0 < (51 / 2 ^ 3 : ℚ) ∧ seg0_2_3.a ≤ 51 / 2 ^ 3 ∧ 7 ≤ seg0_2_3.b := by
  decide +kernel

theorem check_p5_4 :
    ratioCheckI (toInt 134 (pE seg0_3_0 pR5 pS5)) (toInt 54 (sTilde seg0_3_0.c pS5)) 134 54 68 277 (-1) (1) 1 12 = true ∧
      isScaled 134 (pE seg0_3_0 pR5 pS5) = true ∧ isScaled 54 (sTilde seg0_3_0.c pS5) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 1 = 7 - seg0_3_0.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 1 = 8 - seg0_3_0.c ∧
      0 < (7 : ℚ) ∧ seg0_3_0.a ≤ 7 ∧ 8 ≤ seg0_3_0.b := by
  decide +kernel

/-- `pzero` on `[b5, 8]`: within `277/2^68 + 2^-70`, about `2 ^ -59.88`. -/
theorem pzero_5 (x : ℝ) (hlo : (((b5 : ℚ)) : ℝ) ≤ x) (hhi : x ≤ (((8 : ℚ)) : ℝ)) :
    |P0 x - pFd pR5 pS5 x| ≤ 277 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : pR5.length ≤ pS5.length + 1 := by decide
  rcases le_total x (((41 / 2 ^ 3 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast p_step (piece0_2, seg0_2_0) (segs_2_ok.1) (by simp [pieces, last]) pR5 pS5 hR (b5) (41 / 2 ^ 3) 158 78 277 _ _ _ ⟨check_p5_0.2.1, check_p5_0.2.2.1⟩ check_p5_0.1 ⟨check_p5_0.2.2.2.1, check_p5_0.2.2.2.2.1⟩ check_p5_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((23 / 2 ^ 2 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast p_step (piece0_2, seg0_2_1) (segs_2_ok.2.1) (by simp [pieces, last]) pR5 pS5 hR (41 / 2 ^ 3) (23 / 2 ^ 2) 158 78 277 _ _ _ ⟨check_p5_1.2.1, check_p5_1.2.2.1⟩ check_p5_1.1 ⟨check_p5_1.2.2.2.1, check_p5_1.2.2.2.2.1⟩ check_p5_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((51 / 2 ^ 3 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast p_step (piece0_2, seg0_2_2) (segs_2_ok.2.2.1) (by simp [pieces, last]) pR5 pS5 hR (23 / 2 ^ 2) (51 / 2 ^ 3) 158 78 277 _ _ _ ⟨check_p5_2.2.1, check_p5_2.2.2.1⟩ check_p5_2.1 ⟨check_p5_2.2.2.2.1, check_p5_2.2.2.2.2.1⟩ check_p5_2.2.2.2.2.2 x ⟨h1, h2⟩
  rcases le_total x (((7 : ℚ)) : ℝ) with h3 | h3
  · exact_mod_cast p_step (piece0_2, seg0_2_3) (segs_2_ok.2.2.2) (by simp [pieces, last]) pR5 pS5 hR (51 / 2 ^ 3) (7) 158 78 277 _ _ _ ⟨check_p5_3.2.1, check_p5_3.2.2.1⟩ check_p5_3.1 ⟨check_p5_3.2.2.2.1, check_p5_3.2.2.2.2.1⟩ check_p5_3.2.2.2.2.2 x ⟨h2, h3⟩
  exact_mod_cast p_step (piece0_3, seg0_3_0) (segs_3_ok.1) (by simp [pieces, last]) pR5 pS5 hR (7) (8) 134 54 277 _ _ _ ⟨check_p5_4.2.1, check_p5_4.2.2.1⟩ check_p5_4.1 ⟨check_p5_4.2.2.2.1, check_p5_4.2.2.2.2.1⟩ check_p5_4.2.2.2.2.2 x ⟨h3, hhi⟩

theorem check_q5_0 :
    ratioCheckI (toInt 170 (qE (-1 / 8) seg0_2_0 qR5 qS5)) (toInt 90 (qW seg0_2_0 qS5)) 170 90 68 22 (-70005) (81920) 18 12 = true ∧
      isScaled 170 (qE (-1 / 8) seg0_2_0 qR5 qS5) = true ∧ isScaled 90 (qW seg0_2_0 qS5) = true ∧
      ((-70005 : ℤ) : ℚ) / 2 ^ 18 = b5 - seg0_2_0.c ∧ ((81920 : ℤ) : ℚ) / 2 ^ 18 = 41 / 2 ^ 3 - seg0_2_0.c ∧
      0 < (b5 : ℚ) ∧ seg0_2_0.a ≤ b5 ∧ 41 / 2 ^ 3 ≤ seg0_2_0.b := by
  decide +kernel

theorem check_q5_1 :
    ratioCheckI (toInt 170 (qE (-1 / 8) seg0_2_1 qR5 qS5)) (toInt 90 (qW seg0_2_1 qS5)) 170 90 68 22 (-5) (5) 4 12 = true ∧
      isScaled 170 (qE (-1 / 8) seg0_2_1 qR5 qS5) = true ∧ isScaled 90 (qW seg0_2_1 qS5) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 4 = 41 / 2 ^ 3 - seg0_2_1.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 4 = 23 / 2 ^ 2 - seg0_2_1.c ∧
      0 < (41 / 2 ^ 3 : ℚ) ∧ seg0_2_1.a ≤ 41 / 2 ^ 3 ∧ 23 / 2 ^ 2 ≤ seg0_2_1.b := by
  decide +kernel

theorem check_q5_2 :
    ratioCheckI (toInt 170 (qE (-1 / 8) seg0_2_2 qR5 qS5)) (toInt 90 (qW seg0_2_2 qS5)) 170 90 68 22 (-5) (5) 4 12 = true ∧
      isScaled 170 (qE (-1 / 8) seg0_2_2 qR5 qS5) = true ∧ isScaled 90 (qW seg0_2_2 qS5) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 4 = 23 / 2 ^ 2 - seg0_2_2.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 4 = 51 / 2 ^ 3 - seg0_2_2.c ∧
      0 < (23 / 2 ^ 2 : ℚ) ∧ seg0_2_2.a ≤ 23 / 2 ^ 2 ∧ 51 / 2 ^ 3 ≤ seg0_2_2.b := by
  decide +kernel

theorem check_q5_3 :
    ratioCheckI (toInt 170 (qE (-1 / 8) seg0_2_3 qR5 qS5)) (toInt 90 (qW seg0_2_3 qS5)) 170 90 68 22 (-5) (5) 4 12 = true ∧
      isScaled 170 (qE (-1 / 8) seg0_2_3 qR5 qS5) = true ∧ isScaled 90 (qW seg0_2_3 qS5) = true ∧
      ((-5 : ℤ) : ℚ) / 2 ^ 4 = 51 / 2 ^ 3 - seg0_2_3.c ∧ ((5 : ℤ) : ℚ) / 2 ^ 4 = 7 - seg0_2_3.c ∧
      0 < (51 / 2 ^ 3 : ℚ) ∧ seg0_2_3.a ≤ 51 / 2 ^ 3 ∧ 7 ≤ seg0_2_3.b := by
  decide +kernel

theorem check_q5_4 :
    ratioCheckI (toInt 137 (qE (-1 / 8) seg0_3_0 qR5 qS5)) (toInt 57 (qW seg0_3_0 qS5)) 137 57 68 22 (-1) (1) 1 12 = true ∧
      isScaled 137 (qE (-1 / 8) seg0_3_0 qR5 qS5) = true ∧ isScaled 57 (qW seg0_3_0 qS5) = true ∧
      ((-1 : ℤ) : ℚ) / 2 ^ 1 = 7 - seg0_3_0.c ∧ ((1 : ℤ) : ℚ) / 2 ^ 1 = 8 - seg0_3_0.c ∧
      0 < (7 : ℚ) ∧ seg0_3_0.a ≤ 7 ∧ 8 ≤ seg0_3_0.b := by
  decide +kernel

/-- `qzero` on `[b5, 8]`: within `22/2^68 + 2^-70`, about `2 ^ -63.52`. -/
theorem qzero_5 (x : ℝ) (hlo : (((b5 : ℚ)) : ℝ) ≤ x) (hhi : x ≤ (((8 : ℚ)) : ℝ)) :
    |Q0 x - qFd (-1 / 8) qR5 qS5 x| ≤ 22 / 2 ^ 68 + 1 / 2 ^ 70 := by
  have hR : qR5.length ≤ qS5.length + 1 := by decide
  rcases le_total x (((41 / 2 ^ 3 : ℚ)) : ℝ) with h0 | h0
  · exact_mod_cast q_step (piece0_2, seg0_2_0) (segs_2_ok.1) (by simp [pieces, last]) qR5 qS5 hR (b5) (41 / 2 ^ 3) 170 90 22 _ _ _ ⟨check_q5_0.2.1, check_q5_0.2.2.1⟩ check_q5_0.1 ⟨check_q5_0.2.2.2.1, check_q5_0.2.2.2.2.1⟩ check_q5_0.2.2.2.2.2 x ⟨hlo, h0⟩
  rcases le_total x (((23 / 2 ^ 2 : ℚ)) : ℝ) with h1 | h1
  · exact_mod_cast q_step (piece0_2, seg0_2_1) (segs_2_ok.2.1) (by simp [pieces, last]) qR5 qS5 hR (41 / 2 ^ 3) (23 / 2 ^ 2) 170 90 22 _ _ _ ⟨check_q5_1.2.1, check_q5_1.2.2.1⟩ check_q5_1.1 ⟨check_q5_1.2.2.2.1, check_q5_1.2.2.2.2.1⟩ check_q5_1.2.2.2.2.2 x ⟨h0, h1⟩
  rcases le_total x (((51 / 2 ^ 3 : ℚ)) : ℝ) with h2 | h2
  · exact_mod_cast q_step (piece0_2, seg0_2_2) (segs_2_ok.2.2.1) (by simp [pieces, last]) qR5 qS5 hR (23 / 2 ^ 2) (51 / 2 ^ 3) 170 90 22 _ _ _ ⟨check_q5_2.2.1, check_q5_2.2.2.1⟩ check_q5_2.1 ⟨check_q5_2.2.2.2.1, check_q5_2.2.2.2.2.1⟩ check_q5_2.2.2.2.2.2 x ⟨h1, h2⟩
  rcases le_total x (((7 : ℚ)) : ℝ) with h3 | h3
  · exact_mod_cast q_step (piece0_2, seg0_2_3) (segs_2_ok.2.2.2) (by simp [pieces, last]) qR5 qS5 hR (51 / 2 ^ 3) (7) 170 90 22 _ _ _ ⟨check_q5_3.2.1, check_q5_3.2.2.1⟩ check_q5_3.1 ⟨check_q5_3.2.2.2.1, check_q5_3.2.2.2.2.1⟩ check_q5_3.2.2.2.2.2 x ⟨h2, h3⟩
  exact_mod_cast q_step (piece0_3, seg0_3_0) (segs_3_ok.1) (by simp [pieces, last]) qR5 qS5 hR (7) (8) 137 57 22 _ _ _ ⟨check_q5_4.2.1, check_q5_4.2.2.1⟩ check_q5_4.1 ⟨check_q5_4.2.2.2.1, check_q5_4.2.2.2.2.1⟩ check_q5_4.2.2.2.2.2 x ⟨h3, hhi⟩

#print axioms pzero_2
#print axioms qzero_2
#print axioms pzero_3
#print axioms qzero_3
#print axioms pzero_5
#print axioms qzero_5

end LeanExe.ProofKit.BesselFd0a
