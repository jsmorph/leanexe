import Library.Numerics.Float64.Lgamma.LgammaRootSpec

/-!
The kernel checks of the 17 polynomials of `Lgamma.accurate` about the negative zeros, the inputs
of `LgammaRootSpec.root_spec`: the steps of the double-double part on one interval each side of 0
(`rok`), the bound of the double tail (`tok`, `tl`), the range of the polynomial (`rp`, `rn`), its
Lipschitz constant on `[-1, 1]` (`lp`), and the numeric conditions (`num`).  A script computed the
step bounds as powers of two and checked every condition in exact arithmetic before the kernel.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaRootKern
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

local notation "tab" => Lgamma.accurateTable

/-! ### Range 0: `(PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) < x < (-2 : ℚ)`, offset 128 -/

def C0 : List ℚ := LgammaPolyIv.pz [-1, 0, 5, 5, 9, 10, 13, 14, 17, 18, 21, 22, 25, 26, 29, 30, 32, 34, 36, 38]
def Cl0 : List ℚ := LgammaPolyIv.pz [54, 54, 60, 59, 63, 65, 67, 69, 72, 76, 75, 77, 80, 81, 83, 86, 86, 89, 91, 93]
def E0 : List ℚ := LgammaPolyIv.pz [79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79]
def L0 : List ℚ := LgammaPolyIv.pz [41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41, 41]
def K0 : List ℚ := LgammaPolyIv.pz [38, 36, 34, 32, 30, 28, 26, 24, 22, 21, 18, 17, 14, 13, 10, 9, 5, 5, 0]

theorem rok0 : LgammaRootEval.rootIvOk tab 131 20 6 1 (437951 / 2 ^ 20 : ℚ) (695117 / 2 ^ 20 : ℚ) (764289224164770471 / 2 ^ 60 : ℚ) (679 / 2 ^ 60 : ℚ) C0 Cl0 E0 L0 K0 = true := by
  decide +kernel

theorem tok0 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 171 6 (6 - 1)) (764289224164770471 / 2 ^ 60 : ℚ) = true := by
  decide +kernel

theorem tl0 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (764289224164770471 / 2 ^ 60 : ℚ) (0 :: LgammaRootPath.tailList tab 171 6) ≤ (1 / 2 ^ 29 : ℚ) := by
  decide +kernel

theorem rp0 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 131 20) (20 + 6) 1 (437951 / 2 ^ 20 : ℚ) (1167087 / 2 ^ 20 : ℚ) (465145 / 2 ^ 18 : ℚ) = true := by
  decide +kernel

theorem rn0 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 131 20) (20 + 6) 1 (695117 / 2 ^ 20 : ℚ) (1167087 / 2 ^ 20 : ℚ) (465145 / 2 ^ 18 : ℚ) = true := by
  decide +kernel

theorem lp0 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 131 20 ++ LgammaApprox.coeffs tab 171 2 6) ≤ (186869 / 2 ^ 18 : ℚ) := by
  decide +kernel

theorem num0 :
    ((764289224164770471 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 171 6 (764289224164770471 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 171 6 (764289224164770471 / 2 ^ 60 : ℚ)) ≤ 1) ∧
    ((764289224164770471 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 171 6 (764289224164770471 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 171 6 (764289224164770471 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[131 + 2 * (20 - 1)]!)) ∧
    (((764289224164770471 / 2 ^ 60 : ℚ) * LgammaRootPath.tE tab 171 6 (764289224164770471 / 2 ^ 60 : ℚ) + (764289224164770471 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 171 6 (764289224164770471 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 171 6 (764289224164770471 / 2 ^ 60 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (1 / 2 ^ 29 : ℚ) * (679 / 2 ^ 60 : ℚ)) + ((764289224164770471 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 171 6 (764289224164770471 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 171 6 (764289224164770471 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl0).getD (20 - 1) 0) / 2 ^ 53 ≤ (E0).getD 0 0) ∧
    (((764289224164770471 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 171 6 (764289224164770471 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 171 6 (764289224164770471 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl0).getD (20 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L0).getD 0 0) ∧
    (2 ^ 1 ≤ LgammaApprox.q tab 128) ∧
    (PolyBound.qabs (LgammaApprox.q tab (128 + 1)) ≤ 2 ^ 1 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (128 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 1 ≤ -(-44361043621697138841 / 2 ^ 64 : ℚ)) ∧
    (-(-46852683983129509919 / 2 ^ 64 : ℚ) < 2 ^ (1 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 128 + (-46852683983129509919 / 2 ^ 64 : ℚ)) ∧
    (LgammaApprox.q tab 128 + (-44361043621697138841 / 2 ^ 64 : ℚ) ≤ 1 / 2) ∧
    (-(695117 / 2 ^ 20 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 3 * ((-46852683983129509919 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 128)) ∧
    (2 ^ 3 * ((-44361043621697138841 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 128) ≤ (437951 / 2 ^ 20 : ℚ) - 1 / 2 ^ 40) ∧
    ((437951 / 2 ^ 20 : ℚ) ≤ 1 ∧ (695117 / 2 ^ 20 : ℚ) ≤ 1 ∧ 0 ≤ (437951 / 2 ^ 20 : ℚ) ∧ 0 ≤ (695117 / 2 ^ 20 : ℚ)) ∧
    ((437951 / 2 ^ 20 : ℚ) + (679 / 2 ^ 60 : ℚ) ≤ (764289224164770471 / 2 ^ 60 : ℚ) ∧ (695117 / 2 ^ 20 : ℚ) + (679 / 2 ^ 60 : ℚ) ≤ (764289224164770471 / 2 ^ 60 : ℚ)) ∧
    ((437951 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 3 / 2 ^ 99 ≤ (679 / 2 ^ 60 : ℚ) ∧ (695117 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 3 / 2 ^ 99 ≤ (679 / 2 ^ 60 : ℚ)) ∧
    ((764289224164770471 / 2 ^ 60 : ℚ) ≤ (764289224164770471 / 2 ^ 60 : ℚ) ∧ (764289224164770471 / 2 ^ 60 : ℚ) ≤ (764289224164770471 / 2 ^ 60 : ℚ)) ∧
    ((465145 / 2 ^ 18 : ℚ) ≤ 2 * (1167087 / 2 ^ 20 : ℚ)) ∧
    ((186869 / 2 ^ 18 : ℚ) ≤ (1167087 / 2 ^ 20 : ℚ)) ∧
    ((E0).getD (20 - 1) 0 ≤ (1167087 / 2 ^ 20 : ℚ) / 2 ^ 70) ∧
    ((L0).getD (20 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((465145 / 2 ^ 18 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (1167087 / 2 ^ 20 : ℚ)) ∧
    (0 < (1167087 / 2 ^ 20 : ℚ) ∧ ((1167087 / 2 ^ 20 : ℚ) ≤ (1167087 / 2 ^ 20 : ℚ) ∧ (465145 / 2 ^ 18 : ℚ) ≤ (465145 / 2 ^ 18 : ℚ))) := by
  decide +kernel

/-! ### Range 1: `(-3 : ℚ) < x < (PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ)`, offset 183 -/

def C1 : List ℚ := LgammaPolyIv.pz [-1, 0, 3, 6, 8, 10, 12, 15, 17, 19, 21, 23, 25, 27, 30, 32, 34, 36, 38, 40, 42]
def Cl1 : List ℚ := LgammaPolyIv.pz [53, 54, 58, 61, 62, 65, 68, 70, 74, 76, 76, 81, 81, 81, 84, 87, 89, 90, 92, 94, 97]
def E1 : List ℚ := LgammaPolyIv.pz [79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79]
def L1 : List ℚ := LgammaPolyIv.pz [44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44]
def K1 : List ℚ := LgammaPolyIv.pz [42, 40, 38, 36, 34, 32, 29, 27, 25, 23, 21, 19, 17, 14, 12, 10, 8, 5, 3, 0]

theorem rok1 : LgammaRootEval.rootIvOk tab 186 21 6 1 (384727 / 2 ^ 19 : ℚ) (260515 / 2 ^ 19 : ℚ) (52876476252422191 / 2 ^ 56 : ℚ) (47 / 2 ^ 56 : ℚ) C1 Cl1 E1 L1 K1 = true := by
  decide +kernel

theorem tok1 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 228 6 (6 - 1)) (52876476252422191 / 2 ^ 56 : ℚ) = true := by
  decide +kernel

theorem tl1 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (52876476252422191 / 2 ^ 56 : ℚ) (0 :: LgammaRootPath.tailList tab 228 6) ≤ (1 / 2 ^ 29 : ℚ) := by
  decide +kernel

theorem rp1 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 186 21) (21 + 6) 1 (384727 / 2 ^ 19 : ℚ) (-1170827 / 2 ^ 19 : ℚ) (-773431 / 2 ^ 19 : ℚ) = true := by
  decide +kernel

theorem rn1 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 186 21) (21 + 6) 1 (260515 / 2 ^ 19 : ℚ) (-1170827 / 2 ^ 19 : ℚ) (-773431 / 2 ^ 19 : ℚ) = true := by
  decide +kernel

theorem lp1 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 186 21 ++ LgammaApprox.coeffs tab 228 2 6) ≤ (857037 / 2 ^ 20 : ℚ) := by
  decide +kernel

theorem num1 :
    ((52876476252422191 / 2 ^ 56 : ℚ) * (LgammaRootPath.tM tab 228 6 (52876476252422191 / 2 ^ 56 : ℚ) + LgammaRootPath.tE tab 228 6 (52876476252422191 / 2 ^ 56 : ℚ)) ≤ 1) ∧
    ((52876476252422191 / 2 ^ 56 : ℚ) * (LgammaRootPath.tM tab 228 6 (52876476252422191 / 2 ^ 56 : ℚ) + LgammaRootPath.tE tab 228 6 (52876476252422191 / 2 ^ 56 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[186 + 2 * (21 - 1)]!)) ∧
    (((52876476252422191 / 2 ^ 56 : ℚ) * LgammaRootPath.tE tab 228 6 (52876476252422191 / 2 ^ 56 : ℚ) + (52876476252422191 / 2 ^ 56 : ℚ) * (LgammaRootPath.tM tab 228 6 (52876476252422191 / 2 ^ 56 : ℚ) + LgammaRootPath.tE tab 228 6 (52876476252422191 / 2 ^ 56 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (1 / 2 ^ 29 : ℚ) * (47 / 2 ^ 56 : ℚ)) + ((52876476252422191 / 2 ^ 56 : ℚ) * (LgammaRootPath.tM tab 228 6 (52876476252422191 / 2 ^ 56 : ℚ) + LgammaRootPath.tE tab 228 6 (52876476252422191 / 2 ^ 56 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl1).getD (21 - 1) 0) / 2 ^ 53 ≤ (E1).getD 0 0) ∧
    (((52876476252422191 / 2 ^ 56 : ℚ) * (LgammaRootPath.tM tab 228 6 (52876476252422191 / 2 ^ 56 : ℚ) + LgammaRootPath.tE tab 228 6 (52876476252422191 / 2 ^ 56 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl1).getD (21 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L1).getD 0 0) ∧
    (2 ^ 1 ≤ LgammaApprox.q tab 183) ∧
    (PolyBound.qabs (LgammaApprox.q tab (183 + 1)) ≤ 2 ^ 1 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (183 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 1 ≤ -(-49839775541959449833 / 2 ^ 64 : ℚ)) ∧
    (-(-25629338539291882257 / 2 ^ 63 : ℚ) < 2 ^ (1 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 183 + (-25629338539291882257 / 2 ^ 63 : ℚ)) ∧
    (LgammaApprox.q tab 183 + (-49839775541959449833 / 2 ^ 64 : ℚ) ≤ 1 / 2) ∧
    (-(260515 / 2 ^ 19 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 4 * ((-25629338539291882257 / 2 ^ 63 : ℚ) + LgammaApprox.rootX0 183)) ∧
    (2 ^ 4 * ((-49839775541959449833 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 183) ≤ (384727 / 2 ^ 19 : ℚ) - 1 / 2 ^ 40) ∧
    ((384727 / 2 ^ 19 : ℚ) ≤ 1 ∧ (260515 / 2 ^ 19 : ℚ) ≤ 1 ∧ 0 ≤ (384727 / 2 ^ 19 : ℚ) ∧ 0 ≤ (260515 / 2 ^ 19 : ℚ)) ∧
    ((384727 / 2 ^ 19 : ℚ) + (47 / 2 ^ 56 : ℚ) ≤ (52876476252422191 / 2 ^ 56 : ℚ) ∧ (260515 / 2 ^ 19 : ℚ) + (47 / 2 ^ 56 : ℚ) ≤ (52876476252422191 / 2 ^ 56 : ℚ)) ∧
    ((384727 / 2 ^ 19 : ℚ) / 2 ^ 50 + 2 ^ 4 / 2 ^ 99 ≤ (47 / 2 ^ 56 : ℚ) ∧ (260515 / 2 ^ 19 : ℚ) / 2 ^ 50 + 2 ^ 4 / 2 ^ 99 ≤ (47 / 2 ^ 56 : ℚ)) ∧
    ((52876476252422191 / 2 ^ 56 : ℚ) ≤ (52876476252422191 / 2 ^ 56 : ℚ) ∧ (52876476252422191 / 2 ^ 56 : ℚ) ≤ (52876476252422191 / 2 ^ 56 : ℚ)) ∧
    ((1170827 / 2 ^ 19 : ℚ) ≤ 2 * (773431 / 2 ^ 19 : ℚ)) ∧
    ((857037 / 2 ^ 20 : ℚ) ≤ (773431 / 2 ^ 19 : ℚ)) ∧
    ((E1).getD (21 - 1) 0 ≤ (773431 / 2 ^ 19 : ℚ) / 2 ^ 70) ∧
    ((L1).getD (21 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((1170827 / 2 ^ 19 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (773431 / 2 ^ 19 : ℚ)) ∧
    (0 < (773431 / 2 ^ 19 : ℚ) ∧ (-(1170827 / 2 ^ 19 : ℚ) ≤ (-1170827 / 2 ^ 19 : ℚ) ∧ (-773431 / 2 ^ 19 : ℚ) ≤ -(773431 / 2 ^ 19 : ℚ))) := by
  decide +kernel

/-! ### Range 2: `(-7 / 2 : ℚ) < x < (-3 : ℚ)`, offset 240 -/

def C2 : List ℚ := LgammaPolyIv.pz [-3, 1, 5, 8, 12, 15, 19, 22, 25, 29, 32, 35, 39]
def Cl2 : List ℚ := LgammaPolyIv.pz [52, 55, 60, 62, 67, 72, 77, 78, 79, 83, 88, 89, 94]
def E2 : List ℚ := LgammaPolyIv.pz [79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79]
def L2 : List ℚ := LgammaPolyIv.pz [43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43]
def K2 : List ℚ := LgammaPolyIv.pz [39, 35, 32, 29, 25, 22, 19, 15, 12, 8, 5, 1]

theorem rok2 : LgammaRootEval.rootIvOk tab 243 13 7 1 (626683 / 2 ^ 20 : ℚ) (668109 / 2 ^ 20 : ℚ) (734593614121796237 / 2 ^ 60 : ℚ) (653 / 2 ^ 60 : ℚ) C2 Cl2 E2 L2 K2 = true := by
  decide +kernel

theorem tok2 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 269 7 (7 - 1)) (734593614121796237 / 2 ^ 60 : ℚ) = true := by
  decide +kernel

theorem tl2 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (734593614121796237 / 2 ^ 60 : ℚ) (0 :: LgammaRootPath.tailList tab 269 7) ≤ (1 / 2 ^ 29 : ℚ) := by
  decide +kernel

theorem rp2 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 243 13) (13 + 7) 1 (626683 / 2 ^ 20 : ℚ) (3945119 / 2 ^ 19 : ℚ) (8423633 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem rn2 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 243 13) (13 + 7) 1 (668109 / 2 ^ 20 : ℚ) (3945119 / 2 ^ 19 : ℚ) (8423633 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem lp2 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 243 13 ++ LgammaApprox.coeffs tab 269 2 7) ≤ (488693 / 2 ^ 20 : ℚ) := by
  decide +kernel

theorem num2 :
    ((734593614121796237 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 269 7 (734593614121796237 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 269 7 (734593614121796237 / 2 ^ 60 : ℚ)) ≤ 1) ∧
    ((734593614121796237 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 269 7 (734593614121796237 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 269 7 (734593614121796237 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[243 + 2 * (13 - 1)]!)) ∧
    (((734593614121796237 / 2 ^ 60 : ℚ) * LgammaRootPath.tE tab 269 7 (734593614121796237 / 2 ^ 60 : ℚ) + (734593614121796237 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 269 7 (734593614121796237 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 269 7 (734593614121796237 / 2 ^ 60 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (1 / 2 ^ 29 : ℚ) * (653 / 2 ^ 60 : ℚ)) + ((734593614121796237 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 269 7 (734593614121796237 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 269 7 (734593614121796237 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl2).getD (13 - 1) 0) / 2 ^ 53 ≤ (E2).getD 0 0) ∧
    (((734593614121796237 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 269 7 (734593614121796237 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 269 7 (734593614121796237 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl2).getD (13 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L2).getD 0 0) ∧
    (2 ^ 1 ≤ LgammaApprox.q tab 240) ∧
    (PolyBound.qabs (LgammaApprox.q tab (240 + 1)) ≤ 2 ^ 1 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (240 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 1 ≤ -(-7227071362634278469 / 2 ^ 61 : ℚ)) ∧
    (-(-58172480345658311775 / 2 ^ 64 : ℚ) < 2 ^ (1 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 240 + (-58172480345658311775 / 2 ^ 64 : ℚ)) ∧
    (LgammaApprox.q tab 240 + (-7227071362634278469 / 2 ^ 61 : ℚ) ≤ 1 / 2) ∧
    (-(668109 / 2 ^ 20 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 6 * ((-58172480345658311775 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 240)) ∧
    (2 ^ 6 * ((-7227071362634278469 / 2 ^ 61 : ℚ) + LgammaApprox.rootX0 240) ≤ (626683 / 2 ^ 20 : ℚ) - 1 / 2 ^ 40) ∧
    ((626683 / 2 ^ 20 : ℚ) ≤ 1 ∧ (668109 / 2 ^ 20 : ℚ) ≤ 1 ∧ 0 ≤ (626683 / 2 ^ 20 : ℚ) ∧ 0 ≤ (668109 / 2 ^ 20 : ℚ)) ∧
    ((626683 / 2 ^ 20 : ℚ) + (653 / 2 ^ 60 : ℚ) ≤ (734593614121796237 / 2 ^ 60 : ℚ) ∧ (668109 / 2 ^ 20 : ℚ) + (653 / 2 ^ 60 : ℚ) ≤ (734593614121796237 / 2 ^ 60 : ℚ)) ∧
    ((626683 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 6 / 2 ^ 99 ≤ (653 / 2 ^ 60 : ℚ) ∧ (668109 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 6 / 2 ^ 99 ≤ (653 / 2 ^ 60 : ℚ)) ∧
    ((734593614121796237 / 2 ^ 60 : ℚ) ≤ (734593614121796237 / 2 ^ 60 : ℚ) ∧ (734593614121796237 / 2 ^ 60 : ℚ) ≤ (734593614121796237 / 2 ^ 60 : ℚ)) ∧
    ((8423633 / 2 ^ 20 : ℚ) ≤ 2 * (3945119 / 2 ^ 19 : ℚ)) ∧
    ((488693 / 2 ^ 20 : ℚ) ≤ (3945119 / 2 ^ 19 : ℚ)) ∧
    ((E2).getD (13 - 1) 0 ≤ (3945119 / 2 ^ 19 : ℚ) / 2 ^ 70) ∧
    ((L2).getD (13 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((8423633 / 2 ^ 20 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (3945119 / 2 ^ 19 : ℚ)) ∧
    (0 < (3945119 / 2 ^ 19 : ℚ) ∧ ((3945119 / 2 ^ 19 : ℚ) ≤ (3945119 / 2 ^ 19 : ℚ) ∧ (8423633 / 2 ^ 20 : ℚ) ≤ (8423633 / 2 ^ 20 : ℚ))) := by
  decide +kernel

/-! ### Range 3: `(-4 : ℚ) < x < (-7 / 2 : ℚ)`, offset 283 -/

def C3 : List ℚ := LgammaPolyIv.pz [-5, 0, 4, 8, 11, 15, 19, 23, 26, 30, 34, 37, 41]
def Cl3 : List ℚ := LgammaPolyIv.pz [49, 54, 59, 64, 67, 69, 73, 77, 81, 85, 90, 91, 99]
def E3 : List ℚ := LgammaPolyIv.pz [79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79]
def L3 : List ℚ := LgammaPolyIv.pz [45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 44]
def K3 : List ℚ := LgammaPolyIv.pz [41, 37, 34, 30, 26, 23, 19, 15, 11, 7, 4, -1]

theorem rok3 : LgammaRootEval.rootIvOk tab 286 13 7 1 (206989 / 2 ^ 18 : ℚ) (385123 / 2 ^ 19 : ℚ) (910347249286906665 / 2 ^ 60 : ℚ) (809 / 2 ^ 60 : ℚ) C3 Cl3 E3 L3 K3 = true := by
  decide +kernel

theorem tok3 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 312 7 (7 - 1)) (910347249286906665 / 2 ^ 60 : ℚ) = true := by
  decide +kernel

theorem tl3 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (910347249286906665 / 2 ^ 60 : ℚ) (0 :: LgammaRootPath.tailList tab 312 7) ≤ (1 / 2 ^ 29 : ℚ) := by
  decide +kernel

theorem rp3 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 286 13) (13 + 7) 1 (206989 / 2 ^ 18 : ℚ) (-22522997 / 2 ^ 20 : ℚ) (-2614713 / 2 ^ 17 : ℚ) = true := by
  decide +kernel

theorem rn3 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 286 13) (13 + 7) 1 (385123 / 2 ^ 19 : ℚ) (-22522997 / 2 ^ 20 : ℚ) (-2614713 / 2 ^ 17 : ℚ) = true := by
  decide +kernel

theorem lp3 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 286 13 ++ LgammaApprox.coeffs tab 312 2 7) ≤ (581671 / 2 ^ 19 : ℚ) := by
  decide +kernel

theorem num3 :
    ((910347249286906665 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 312 7 (910347249286906665 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 312 7 (910347249286906665 / 2 ^ 60 : ℚ)) ≤ 1) ∧
    ((910347249286906665 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 312 7 (910347249286906665 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 312 7 (910347249286906665 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[286 + 2 * (13 - 1)]!)) ∧
    (((910347249286906665 / 2 ^ 60 : ℚ) * LgammaRootPath.tE tab 312 7 (910347249286906665 / 2 ^ 60 : ℚ) + (910347249286906665 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 312 7 (910347249286906665 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 312 7 (910347249286906665 / 2 ^ 60 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (1 / 2 ^ 29 : ℚ) * (809 / 2 ^ 60 : ℚ)) + ((910347249286906665 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 312 7 (910347249286906665 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 312 7 (910347249286906665 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl3).getD (13 - 1) 0) / 2 ^ 53 ≤ (E3).getD 0 0) ∧
    (((910347249286906665 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 312 7 (910347249286906665 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 312 7 (910347249286906665 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl3).getD (13 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L3).getD 0 0) ∧
    (2 ^ 1 ≤ LgammaApprox.q tab 283) ∧
    (PolyBound.qabs (LgammaApprox.q tab (283 + 1)) ≤ 2 ^ 1 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (283 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 1 ≤ -(-36452702367154859857 / 2 ^ 63 : ℚ)) ∧
    (-(-36507616132442691657 / 2 ^ 63 : ℚ) < 2 ^ (1 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 283 + (-36507616132442691657 / 2 ^ 63 : ℚ)) ∧
    (LgammaApprox.q tab 283 + (-36452702367154859857 / 2 ^ 63 : ℚ) ≤ 1 / 2) ∧
    (-(385123 / 2 ^ 19 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 8 * ((-36507616132442691657 / 2 ^ 63 : ℚ) + LgammaApprox.rootX0 283)) ∧
    (2 ^ 8 * ((-36452702367154859857 / 2 ^ 63 : ℚ) + LgammaApprox.rootX0 283) ≤ (206989 / 2 ^ 18 : ℚ) - 1 / 2 ^ 40) ∧
    ((206989 / 2 ^ 18 : ℚ) ≤ 1 ∧ (385123 / 2 ^ 19 : ℚ) ≤ 1 ∧ 0 ≤ (206989 / 2 ^ 18 : ℚ) ∧ 0 ≤ (385123 / 2 ^ 19 : ℚ)) ∧
    ((206989 / 2 ^ 18 : ℚ) + (809 / 2 ^ 60 : ℚ) ≤ (910347249286906665 / 2 ^ 60 : ℚ) ∧ (385123 / 2 ^ 19 : ℚ) + (809 / 2 ^ 60 : ℚ) ≤ (910347249286906665 / 2 ^ 60 : ℚ)) ∧
    ((206989 / 2 ^ 18 : ℚ) / 2 ^ 50 + 2 ^ 8 / 2 ^ 99 ≤ (809 / 2 ^ 60 : ℚ) ∧ (385123 / 2 ^ 19 : ℚ) / 2 ^ 50 + 2 ^ 8 / 2 ^ 99 ≤ (809 / 2 ^ 60 : ℚ)) ∧
    ((910347249286906665 / 2 ^ 60 : ℚ) ≤ (910347249286906665 / 2 ^ 60 : ℚ) ∧ (910347249286906665 / 2 ^ 60 : ℚ) ≤ (910347249286906665 / 2 ^ 60 : ℚ)) ∧
    ((22522997 / 2 ^ 20 : ℚ) ≤ 2 * (2614713 / 2 ^ 17 : ℚ)) ∧
    ((581671 / 2 ^ 19 : ℚ) ≤ (2614713 / 2 ^ 17 : ℚ)) ∧
    ((E3).getD (13 - 1) 0 ≤ (2614713 / 2 ^ 17 : ℚ) / 2 ^ 70) ∧
    ((L3).getD (13 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((22522997 / 2 ^ 20 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (2614713 / 2 ^ 17 : ℚ)) ∧
    (0 < (2614713 / 2 ^ 17 : ℚ) ∧ (-(22522997 / 2 ^ 20 : ℚ) ≤ (-22522997 / 2 ^ 20 : ℚ) ∧ (-2614713 / 2 ^ 17 : ℚ) ≤ -(2614713 / 2 ^ 17 : ℚ))) := by
  decide +kernel

/-! ### Range 4: `(-9 / 2 : ℚ) < x < (-4 : ℚ)`, offset 326 -/

def C4 : List ℚ := LgammaPolyIv.pz [-5, -2, 1, 4, 6, 9, 12, 14, 17, 19, 22, 24, 27, 29, 31, 34, 36]
def Cl4 : List ℚ := LgammaPolyIv.pz [50, 55, 56, 61, 60, 63, 66, 69, 72, 74, 79, 78, 81, 84, 89, 88, 94]
def E4 : List ℚ := LgammaPolyIv.pz [79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79]
def L4 : List ℚ := LgammaPolyIv.pz [39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39]
def K4 : List ℚ := LgammaPolyIv.pz [36, 34, 31, 29, 26, 24, 21, 19, 17, 14, 11, 9, 6, 4, 1, -2]

theorem rok4 : LgammaRootEval.rootIvOk tab 329 17 7 1 (603229 / 2 ^ 20 : ℚ) (676873 / 2 ^ 20 : ℚ) (372114867013812555 / 2 ^ 59 : ℚ) (331 / 2 ^ 59 : ℚ) C4 Cl4 E4 L4 K4 = true := by
  decide +kernel

theorem tok4 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 363 7 (7 - 1)) (372114867013812555 / 2 ^ 59 : ℚ) = true := by
  decide +kernel

theorem tl4 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (372114867013812555 / 2 ^ 59 : ℚ) (0 :: LgammaRootPath.tailList tab 363 7) ≤ (1 / 2 ^ 29 : ℚ) := by
  decide +kernel

theorem rp4 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 329 17) (17 + 7) 1 (603229 / 2 ^ 20 : ℚ) (13188585 / 2 ^ 19 : ℚ) (14873333 / 2 ^ 19 : ℚ) = true := by
  decide +kernel

theorem rn4 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 329 17) (17 + 7) 1 (676873 / 2 ^ 20 : ℚ) (13188585 / 2 ^ 19 : ℚ) (14873333 / 2 ^ 19 : ℚ) = true := by
  decide +kernel

theorem lp4 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 329 17 ++ LgammaApprox.coeffs tab 363 2 7) ≤ (888447 / 2 ^ 18 : ℚ) := by
  decide +kernel

theorem num4 :
    ((372114867013812555 / 2 ^ 59 : ℚ) * (LgammaRootPath.tM tab 363 7 (372114867013812555 / 2 ^ 59 : ℚ) + LgammaRootPath.tE tab 363 7 (372114867013812555 / 2 ^ 59 : ℚ)) ≤ 1) ∧
    ((372114867013812555 / 2 ^ 59 : ℚ) * (LgammaRootPath.tM tab 363 7 (372114867013812555 / 2 ^ 59 : ℚ) + LgammaRootPath.tE tab 363 7 (372114867013812555 / 2 ^ 59 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[329 + 2 * (17 - 1)]!)) ∧
    (((372114867013812555 / 2 ^ 59 : ℚ) * LgammaRootPath.tE tab 363 7 (372114867013812555 / 2 ^ 59 : ℚ) + (372114867013812555 / 2 ^ 59 : ℚ) * (LgammaRootPath.tM tab 363 7 (372114867013812555 / 2 ^ 59 : ℚ) + LgammaRootPath.tE tab 363 7 (372114867013812555 / 2 ^ 59 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (1 / 2 ^ 29 : ℚ) * (331 / 2 ^ 59 : ℚ)) + ((372114867013812555 / 2 ^ 59 : ℚ) * (LgammaRootPath.tM tab 363 7 (372114867013812555 / 2 ^ 59 : ℚ) + LgammaRootPath.tE tab 363 7 (372114867013812555 / 2 ^ 59 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl4).getD (17 - 1) 0) / 2 ^ 53 ≤ (E4).getD 0 0) ∧
    (((372114867013812555 / 2 ^ 59 : ℚ) * (LgammaRootPath.tM tab 363 7 (372114867013812555 / 2 ^ 59 : ℚ) + LgammaRootPath.tE tab 363 7 (372114867013812555 / 2 ^ 59 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl4).getD (17 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L4).getD 0 0) ∧
    (2 ^ 2 ≤ LgammaApprox.q tab 326) ∧
    (PolyBound.qabs (LgammaApprox.q tab (326 + 1)) ≤ 2 ^ 2 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (326 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 2 ≤ -(-74430167010437261973 / 2 ^ 64 : ℚ)) ∧
    (-(-37303051333288377175 / 2 ^ 63 : ℚ) < 2 ^ (2 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 326 + (-37303051333288377175 / 2 ^ 63 : ℚ)) ∧
    (LgammaApprox.q tab 326 + (-74430167010437261973 / 2 ^ 64 : ℚ) ≤ 1 / 2) ∧
    (-(676873 / 2 ^ 20 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 7 * ((-37303051333288377175 / 2 ^ 63 : ℚ) + LgammaApprox.rootX0 326)) ∧
    (2 ^ 7 * ((-74430167010437261973 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 326) ≤ (603229 / 2 ^ 20 : ℚ) - 1 / 2 ^ 40) ∧
    ((603229 / 2 ^ 20 : ℚ) ≤ 1 ∧ (676873 / 2 ^ 20 : ℚ) ≤ 1 ∧ 0 ≤ (603229 / 2 ^ 20 : ℚ) ∧ 0 ≤ (676873 / 2 ^ 20 : ℚ)) ∧
    ((603229 / 2 ^ 20 : ℚ) + (331 / 2 ^ 59 : ℚ) ≤ (372114867013812555 / 2 ^ 59 : ℚ) ∧ (676873 / 2 ^ 20 : ℚ) + (331 / 2 ^ 59 : ℚ) ≤ (372114867013812555 / 2 ^ 59 : ℚ)) ∧
    ((603229 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 7 / 2 ^ 99 ≤ (331 / 2 ^ 59 : ℚ) ∧ (676873 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 7 / 2 ^ 99 ≤ (331 / 2 ^ 59 : ℚ)) ∧
    ((372114867013812555 / 2 ^ 59 : ℚ) ≤ (372114867013812555 / 2 ^ 59 : ℚ) ∧ (372114867013812555 / 2 ^ 59 : ℚ) ≤ (372114867013812555 / 2 ^ 59 : ℚ)) ∧
    ((14873333 / 2 ^ 19 : ℚ) ≤ 2 * (13188585 / 2 ^ 19 : ℚ)) ∧
    ((888447 / 2 ^ 18 : ℚ) ≤ (13188585 / 2 ^ 19 : ℚ)) ∧
    ((E4).getD (17 - 1) 0 ≤ (13188585 / 2 ^ 19 : ℚ) / 2 ^ 70) ∧
    ((L4).getD (17 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((14873333 / 2 ^ 19 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (13188585 / 2 ^ 19 : ℚ)) ∧
    (0 < (13188585 / 2 ^ 19 : ℚ) ∧ ((13188585 / 2 ^ 19 : ℚ) ≤ (13188585 / 2 ^ 19 : ℚ) ∧ (14873333 / 2 ^ 19 : ℚ) ≤ (14873333 / 2 ^ 19 : ℚ))) := by
  decide +kernel

/-! ### Range 5: `(-5 : ℚ) < x < (-9 / 2 : ℚ)`, offset 377 -/

def C5 : List ℚ := LgammaPolyIv.pz [-7, -3, 0, 4, 7, 11, 14, 17, 21, 24, 27, 30]
def Cl5 : List ℚ := LgammaPolyIv.pz [47, 52, 54, 61, 61, 65, 71, 74, 75, 78, 82, 84]
def E5 : List ℚ := LgammaPolyIv.pz [79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79]
def L5 : List ℚ := LgammaPolyIv.pz [34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34]
def K5 : List ℚ := LgammaPolyIv.pz [30, 27, 24, 21, 17, 14, 11, 7, 4, 0, -3]

theorem rok5 : LgammaRootEval.rootIvOk tab 380 12 7 1 (626737 / 2 ^ 20 : ℚ) (585695 / 2 ^ 20 : ℚ) (689104619057447525 / 2 ^ 60 : ℚ) (613 / 2 ^ 60 : ℚ) C5 Cl5 E5 L5 K5 = true := by
  decide +kernel

theorem tok5 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 404 7 (7 - 1)) (689104619057447525 / 2 ^ 60 : ℚ) = true := by
  decide +kernel

theorem tl5 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (689104619057447525 / 2 ^ 60 : ℚ) (0 :: LgammaRootPath.tailList tab 404 7) ≤ (1 / 2 ^ 29 : ℚ) := by
  decide +kernel

theorem rp5 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 380 12) (12 + 7) 1 (626737 / 2 ^ 20 : ℚ) (-63189245 / 2 ^ 19 : ℚ) (-29478801 / 2 ^ 18 : ℚ) = true := by
  decide +kernel

theorem rn5 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 380 12) (12 + 7) 1 (585695 / 2 ^ 20 : ℚ) (-63189245 / 2 ^ 19 : ℚ) (-29478801 / 2 ^ 18 : ℚ) = true := by
  decide +kernel

theorem lp5 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 380 12 ++ LgammaApprox.coeffs tab 404 2 7) ≤ (8429321 / 2 ^ 20 : ℚ) := by
  decide +kernel

theorem num5 :
    ((689104619057447525 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 404 7 (689104619057447525 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 404 7 (689104619057447525 / 2 ^ 60 : ℚ)) ≤ 1) ∧
    ((689104619057447525 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 404 7 (689104619057447525 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 404 7 (689104619057447525 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[380 + 2 * (12 - 1)]!)) ∧
    (((689104619057447525 / 2 ^ 60 : ℚ) * LgammaRootPath.tE tab 404 7 (689104619057447525 / 2 ^ 60 : ℚ) + (689104619057447525 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 404 7 (689104619057447525 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 404 7 (689104619057447525 / 2 ^ 60 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (1 / 2 ^ 29 : ℚ) * (613 / 2 ^ 60 : ℚ)) + ((689104619057447525 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 404 7 (689104619057447525 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 404 7 (689104619057447525 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl5).getD (12 - 1) 0) / 2 ^ 53 ≤ (E5).getD 0 0) ∧
    (((689104619057447525 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 404 7 (689104619057447525 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 404 7 (689104619057447525 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl5).getD (12 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L5).getD 0 0) ∧
    (2 ^ 2 ≤ LgammaApprox.q tab 377) ∧
    (PolyBound.qabs (LgammaApprox.q tab (377 + 1)) ≤ 2 ^ 2 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (377 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 2 ≤ -(-11508372409109077137 / 2 ^ 61 : ℚ)) ∧
    (-(-92087808663733004339 / 2 ^ 64 : ℚ) < 2 ^ (2 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 377 + (-92087808663733004339 / 2 ^ 64 : ℚ)) ∧
    (LgammaApprox.q tab 377 + (-11508372409109077137 / 2 ^ 61 : ℚ) ≤ 1 / 2) ∧
    (-(585695 / 2 ^ 20 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 10 * ((-92087808663733004339 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 377)) ∧
    (2 ^ 10 * ((-11508372409109077137 / 2 ^ 61 : ℚ) + LgammaApprox.rootX0 377) ≤ (626737 / 2 ^ 20 : ℚ) - 1 / 2 ^ 40) ∧
    ((626737 / 2 ^ 20 : ℚ) ≤ 1 ∧ (585695 / 2 ^ 20 : ℚ) ≤ 1 ∧ 0 ≤ (626737 / 2 ^ 20 : ℚ) ∧ 0 ≤ (585695 / 2 ^ 20 : ℚ)) ∧
    ((626737 / 2 ^ 20 : ℚ) + (613 / 2 ^ 60 : ℚ) ≤ (689104619057447525 / 2 ^ 60 : ℚ) ∧ (585695 / 2 ^ 20 : ℚ) + (613 / 2 ^ 60 : ℚ) ≤ (689104619057447525 / 2 ^ 60 : ℚ)) ∧
    ((626737 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 10 / 2 ^ 99 ≤ (613 / 2 ^ 60 : ℚ) ∧ (585695 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 10 / 2 ^ 99 ≤ (613 / 2 ^ 60 : ℚ)) ∧
    ((689104619057447525 / 2 ^ 60 : ℚ) ≤ (689104619057447525 / 2 ^ 60 : ℚ) ∧ (689104619057447525 / 2 ^ 60 : ℚ) ≤ (689104619057447525 / 2 ^ 60 : ℚ)) ∧
    ((63189245 / 2 ^ 19 : ℚ) ≤ 2 * (29478801 / 2 ^ 18 : ℚ)) ∧
    ((8429321 / 2 ^ 20 : ℚ) ≤ (29478801 / 2 ^ 18 : ℚ)) ∧
    ((E5).getD (12 - 1) 0 ≤ (29478801 / 2 ^ 18 : ℚ) / 2 ^ 70) ∧
    ((L5).getD (12 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((63189245 / 2 ^ 19 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (29478801 / 2 ^ 18 : ℚ)) ∧
    (0 < (29478801 / 2 ^ 18 : ℚ) ∧ (-(63189245 / 2 ^ 19 : ℚ) ≤ (-63189245 / 2 ^ 19 : ℚ) ∧ (-29478801 / 2 ^ 18 : ℚ) ≤ -(29478801 / 2 ^ 18 : ℚ))) := by
  decide +kernel

/-! ### Range 6: `(-11 / 2 : ℚ) < x < (-5 : ℚ)`, offset 418 -/

def C6 : List ℚ := LgammaPolyIv.pz [-7, -3, 0, 4, 7, 11, 14, 17, 20, 24, 27, 30, 33]
def Cl6 : List ℚ := LgammaPolyIv.pz [49, 52, 54, 58, 61, 65, 69, 71, 74, 78, 81, 84, 91]
def E6 : List ℚ := LgammaPolyIv.pz [79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79]
def L6 : List ℚ := LgammaPolyIv.pz [37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37, 37]
def K6 : List ℚ := LgammaPolyIv.pz [33, 30, 27, 23, 20, 17, 14, 10, 7, 4, 0, -3]

theorem rok6 : LgammaRootEval.rootIvOk tab 421 13 6 1 (285269 / 2 ^ 19 : ℚ) (609411 / 2 ^ 20 : ℚ) (167513620148650133 / 2 ^ 58 : ℚ) (149 / 2 ^ 58 : ℚ) C6 Cl6 E6 L6 K6 = true := by
  decide +kernel

theorem tok6 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 447 6 (6 - 1)) (167513620148650133 / 2 ^ 58 : ℚ) = true := by
  decide +kernel

theorem tl6 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (167513620148650133 / 2 ^ 58 : ℚ) (0 :: LgammaRootPath.tailList tab 447 6) ≤ (1 / 2 ^ 29 : ℚ) := by
  decide +kernel

theorem rp6 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 421 13) (13 + 6) 1 (285269 / 2 ^ 19 : ℚ) (124947845 / 2 ^ 20 : ℚ) (66833599 / 2 ^ 19 : ℚ) = true := by
  decide +kernel

theorem rn6 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 421 13) (13 + 6) 1 (609411 / 2 ^ 20 : ℚ) (124947845 / 2 ^ 20 : ℚ) (66833599 / 2 ^ 19 : ℚ) = true := by
  decide +kernel

theorem lp6 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 421 13 ++ LgammaApprox.coeffs tab 447 2 6) ≤ (2241845 / 2 ^ 18 : ℚ) := by
  decide +kernel

theorem num6 :
    ((167513620148650133 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 447 6 (167513620148650133 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 447 6 (167513620148650133 / 2 ^ 58 : ℚ)) ≤ 1) ∧
    ((167513620148650133 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 447 6 (167513620148650133 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 447 6 (167513620148650133 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[421 + 2 * (13 - 1)]!)) ∧
    (((167513620148650133 / 2 ^ 58 : ℚ) * LgammaRootPath.tE tab 447 6 (167513620148650133 / 2 ^ 58 : ℚ) + (167513620148650133 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 447 6 (167513620148650133 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 447 6 (167513620148650133 / 2 ^ 58 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (1 / 2 ^ 29 : ℚ) * (149 / 2 ^ 58 : ℚ)) + ((167513620148650133 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 447 6 (167513620148650133 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 447 6 (167513620148650133 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl6).getD (13 - 1) 0) / 2 ^ 53 ≤ (E6).getD 0 0) ∧
    (((167513620148650133 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 447 6 (167513620148650133 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 447 6 (167513620148650133 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl6).getD (13 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L6).getD 0 0) ∧
    (2 ^ 2 ≤ LgammaApprox.q tab 418) ∧
    (PolyBound.qabs (LgammaApprox.q tab (418 + 1)) ≤ 2 ^ 2 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (418 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 2 ≤ -(-92375517059216083221 / 2 ^ 64 : ℚ)) ∧
    (-(-23098947103865220853 / 2 ^ 62 : ℚ) < 2 ^ (2 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 418 + (-23098947103865220853 / 2 ^ 62 : ℚ)) ∧
    (LgammaApprox.q tab 418 + (-92375517059216083221 / 2 ^ 64 : ℚ) ≤ 1 / 2) ∧
    (-(609411 / 2 ^ 20 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 10 * ((-23098947103865220853 / 2 ^ 62 : ℚ) + LgammaApprox.rootX0 418)) ∧
    (2 ^ 10 * ((-92375517059216083221 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 418) ≤ (285269 / 2 ^ 19 : ℚ) - 1 / 2 ^ 40) ∧
    ((285269 / 2 ^ 19 : ℚ) ≤ 1 ∧ (609411 / 2 ^ 20 : ℚ) ≤ 1 ∧ 0 ≤ (285269 / 2 ^ 19 : ℚ) ∧ 0 ≤ (609411 / 2 ^ 20 : ℚ)) ∧
    ((285269 / 2 ^ 19 : ℚ) + (149 / 2 ^ 58 : ℚ) ≤ (167513620148650133 / 2 ^ 58 : ℚ) ∧ (609411 / 2 ^ 20 : ℚ) + (149 / 2 ^ 58 : ℚ) ≤ (167513620148650133 / 2 ^ 58 : ℚ)) ∧
    ((285269 / 2 ^ 19 : ℚ) / 2 ^ 50 + 2 ^ 10 / 2 ^ 99 ≤ (149 / 2 ^ 58 : ℚ) ∧ (609411 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 10 / 2 ^ 99 ≤ (149 / 2 ^ 58 : ℚ)) ∧
    ((167513620148650133 / 2 ^ 58 : ℚ) ≤ (167513620148650133 / 2 ^ 58 : ℚ) ∧ (167513620148650133 / 2 ^ 58 : ℚ) ≤ (167513620148650133 / 2 ^ 58 : ℚ)) ∧
    ((66833599 / 2 ^ 19 : ℚ) ≤ 2 * (124947845 / 2 ^ 20 : ℚ)) ∧
    ((2241845 / 2 ^ 18 : ℚ) ≤ (124947845 / 2 ^ 20 : ℚ)) ∧
    ((E6).getD (13 - 1) 0 ≤ (124947845 / 2 ^ 20 : ℚ) / 2 ^ 70) ∧
    ((L6).getD (13 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((66833599 / 2 ^ 19 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (124947845 / 2 ^ 20 : ℚ)) ∧
    (0 < (124947845 / 2 ^ 20 : ℚ) ∧ ((124947845 / 2 ^ 20 : ℚ) ≤ (124947845 / 2 ^ 20 : ℚ) ∧ (66833599 / 2 ^ 19 : ℚ) ≤ (66833599 / 2 ^ 19 : ℚ))) := by
  decide +kernel

/-! ### Range 7: `(-6 : ℚ) < x < (-11 / 2 : ℚ)`, offset 459 -/

def C7 : List ℚ := LgammaPolyIv.pz [-10, -6, -3, 0, 2, 5, 8, 11, 13, 16, 19, 21, 24, 26, 29, 32, 34, 37]
def Cl7 : List ℚ := LgammaPolyIv.pz [44, 51, 52, 57, 65, 61, 63, 66, 67, 74, 73, 77, 82, 82, 83, 88, 88, 91]
def E7 : List ℚ := LgammaPolyIv.pz [79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79]
def L7 : List ℚ := LgammaPolyIv.pz [40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 39]
def K7 : List ℚ := LgammaPolyIv.pz [37, 34, 31, 29, 26, 24, 21, 18, 16, 13, 10, 8, 5, 2, -1, -4, -7]

theorem rok7 : LgammaRootEval.rootIvOk tab 462 18 6 1 (220135 / 2 ^ 18 : ℚ) (767279 / 2 ^ 20 : ℚ) (242040992180469975 / 2 ^ 58 : ℚ) (215 / 2 ^ 58 : ℚ) C7 Cl7 E7 L7 K7 = true := by
  decide +kernel

theorem tok7 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 498 6 (6 - 1)) (242040992180469975 / 2 ^ 58 : ℚ) = true := by
  decide +kernel

theorem tl7 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (242040992180469975 / 2 ^ 58 : ℚ) (0 :: LgammaRootPath.tailList tab 498 6) ≤ (1 / 2 ^ 29 : ℚ) := by
  decide +kernel

theorem rp7 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 462 18) (18 + 6) 1 (220135 / 2 ^ 18 : ℚ) (-803913787 / 2 ^ 20 : ℚ) (-695605971 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem rn7 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 462 18) (18 + 6) 1 (767279 / 2 ^ 20 : ℚ) (-803913787 / 2 ^ 20 : ℚ) (-695605971 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem lp7 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 462 18 ++ LgammaApprox.coeffs tab 498 2 6) ≤ (2661879 / 2 ^ 15 : ℚ) := by
  decide +kernel

theorem num7 :
    ((242040992180469975 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 498 6 (242040992180469975 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 498 6 (242040992180469975 / 2 ^ 58 : ℚ)) ≤ 1) ∧
    ((242040992180469975 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 498 6 (242040992180469975 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 498 6 (242040992180469975 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[462 + 2 * (18 - 1)]!)) ∧
    (((242040992180469975 / 2 ^ 58 : ℚ) * LgammaRootPath.tE tab 498 6 (242040992180469975 / 2 ^ 58 : ℚ) + (242040992180469975 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 498 6 (242040992180469975 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 498 6 (242040992180469975 / 2 ^ 58 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (1 / 2 ^ 29 : ℚ) * (215 / 2 ^ 58 : ℚ)) + ((242040992180469975 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 498 6 (242040992180469975 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 498 6 (242040992180469975 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl7).getD (18 - 1) 0) / 2 ^ 53 ≤ (E7).getD 0 0) ∧
    (((242040992180469975 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 498 6 (242040992180469975 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 498 6 (242040992180469975 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl7).getD (18 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L7).getD 0 0) ∧
    (2 ^ 2 ≤ LgammaApprox.q tab 459) ∧
    (PolyBound.qabs (LgammaApprox.q tab (459 + 1)) ≤ 2 ^ 2 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (459 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 2 ≤ -(-27662748773484551853 / 2 ^ 62 : ℚ)) ∧
    (-(-110658072421191901135 / 2 ^ 64 : ℚ) < 2 ^ (2 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 459 + (-110658072421191901135 / 2 ^ 64 : ℚ)) ∧
    (LgammaApprox.q tab 459 + (-27662748773484551853 / 2 ^ 62 : ℚ) ≤ 1 / 2) ∧
    (-(767279 / 2 ^ 20 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 12 * ((-110658072421191901135 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 459)) ∧
    (2 ^ 12 * ((-27662748773484551853 / 2 ^ 62 : ℚ) + LgammaApprox.rootX0 459) ≤ (220135 / 2 ^ 18 : ℚ) - 1 / 2 ^ 40) ∧
    ((220135 / 2 ^ 18 : ℚ) ≤ 1 ∧ (767279 / 2 ^ 20 : ℚ) ≤ 1 ∧ 0 ≤ (220135 / 2 ^ 18 : ℚ) ∧ 0 ≤ (767279 / 2 ^ 20 : ℚ)) ∧
    ((220135 / 2 ^ 18 : ℚ) + (215 / 2 ^ 58 : ℚ) ≤ (242040992180469975 / 2 ^ 58 : ℚ) ∧ (767279 / 2 ^ 20 : ℚ) + (215 / 2 ^ 58 : ℚ) ≤ (242040992180469975 / 2 ^ 58 : ℚ)) ∧
    ((220135 / 2 ^ 18 : ℚ) / 2 ^ 50 + 2 ^ 12 / 2 ^ 99 ≤ (215 / 2 ^ 58 : ℚ) ∧ (767279 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 12 / 2 ^ 99 ≤ (215 / 2 ^ 58 : ℚ)) ∧
    ((242040992180469975 / 2 ^ 58 : ℚ) ≤ (242040992180469975 / 2 ^ 58 : ℚ) ∧ (242040992180469975 / 2 ^ 58 : ℚ) ≤ (242040992180469975 / 2 ^ 58 : ℚ)) ∧
    ((803913787 / 2 ^ 20 : ℚ) ≤ 2 * (695605971 / 2 ^ 20 : ℚ)) ∧
    ((2661879 / 2 ^ 15 : ℚ) ≤ (695605971 / 2 ^ 20 : ℚ)) ∧
    ((E7).getD (18 - 1) 0 ≤ (695605971 / 2 ^ 20 : ℚ) / 2 ^ 70) ∧
    ((L7).getD (18 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((803913787 / 2 ^ 20 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (695605971 / 2 ^ 20 : ℚ)) ∧
    (0 < (695605971 / 2 ^ 20 : ℚ) ∧ (-(803913787 / 2 ^ 20 : ℚ) ≤ (-803913787 / 2 ^ 20 : ℚ) ∧ (-695605971 / 2 ^ 20 : ℚ) ≤ -(695605971 / 2 ^ 20 : ℚ))) := by
  decide +kernel

/-! ### Range 8: `(-13 / 2 : ℚ) < x < (-6 : ℚ)`, offset 510 -/

def C8 : List ℚ := LgammaPolyIv.pz [-10, -6, -3, 0, 2, 5, 8, 11, 13, 16, 19, 21, 24, 26, 29, 32, 34, 37]
def Cl8 : List ℚ := LgammaPolyIv.pz [46, 48, 52, 54, 57, 59, 62, 69, 68, 70, 73, 80, 81, 81, 83, 89, 88, 91]
def E8 : List ℚ := LgammaPolyIv.pz [79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79]
def L8 : List ℚ := LgammaPolyIv.pz [39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39, 38]
def K8 : List ℚ := LgammaPolyIv.pz [36, 34, 31, 29, 26, 24, 21, 18, 16, 13, 10, 8, 5, 2, -1, -4, -7]

theorem rok8 : LgammaRootEval.rootIvOk tab 513 18 6 1 (764999 / 2 ^ 20 : ℚ) (438769 / 2 ^ 19 : ℚ) (964863234815296345 / 2 ^ 60 : ℚ) (857 / 2 ^ 60 : ℚ) C8 Cl8 E8 L8 K8 = true := by
  decide +kernel

theorem tok8 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 549 6 (6 - 1)) (964863234815296345 / 2 ^ 60 : ℚ) = true := by
  decide +kernel

theorem tl8 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (964863234815296345 / 2 ^ 60 : ℚ) (0 :: LgammaRootPath.tailList tab 549 6) ≤ (1 / 2 ^ 29 : ℚ) := by
  decide +kernel

theorem rp8 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 513 18) (18 + 6) 1 (764999 / 2 ^ 20 : ℚ) (703072271 / 2 ^ 20 : ℚ) (812174517 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem rn8 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 513 18) (18 + 6) 1 (438769 / 2 ^ 19 : ℚ) (703072271 / 2 ^ 20 : ℚ) (812174517 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem lp8 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 513 18 ++ LgammaApprox.coeffs tab 549 2 6) ≤ (10774549 / 2 ^ 17 : ℚ) := by
  decide +kernel

theorem num8 :
    ((964863234815296345 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 549 6 (964863234815296345 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 549 6 (964863234815296345 / 2 ^ 60 : ℚ)) ≤ 1) ∧
    ((964863234815296345 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 549 6 (964863234815296345 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 549 6 (964863234815296345 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[513 + 2 * (18 - 1)]!)) ∧
    (((964863234815296345 / 2 ^ 60 : ℚ) * LgammaRootPath.tE tab 549 6 (964863234815296345 / 2 ^ 60 : ℚ) + (964863234815296345 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 549 6 (964863234815296345 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 549 6 (964863234815296345 / 2 ^ 60 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (1 / 2 ^ 29 : ℚ) * (857 / 2 ^ 60 : ℚ)) + ((964863234815296345 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 549 6 (964863234815296345 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 549 6 (964863234815296345 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl8).getD (18 - 1) 0) / 2 ^ 53 ≤ (E8).getD 0 0) ∧
    (((964863234815296345 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 549 6 (964863234815296345 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 549 6 (964863234815296345 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl8).getD (18 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L8).getD 0 0) ∧
    (2 ^ 2 ≤ LgammaApprox.q tab 510) ∧
    (PolyBound.qabs (LgammaApprox.q tab (510 + 1)) ≤ 2 ^ 2 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (510 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 2 ≤ -(-110702732972081069923 / 2 ^ 64 : ℚ)) ∧
    (-(-3459680862797579773 / 2 ^ 59 : ℚ) < 2 ^ (2 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 510 + (-3459680862797579773 / 2 ^ 59 : ℚ)) ∧
    (LgammaApprox.q tab 510 + (-110702732972081069923 / 2 ^ 64 : ℚ) ≤ 1 / 2) ∧
    (-(438769 / 2 ^ 19 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 12 * ((-3459680862797579773 / 2 ^ 59 : ℚ) + LgammaApprox.rootX0 510)) ∧
    (2 ^ 12 * ((-110702732972081069923 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 510) ≤ (764999 / 2 ^ 20 : ℚ) - 1 / 2 ^ 40) ∧
    ((764999 / 2 ^ 20 : ℚ) ≤ 1 ∧ (438769 / 2 ^ 19 : ℚ) ≤ 1 ∧ 0 ≤ (764999 / 2 ^ 20 : ℚ) ∧ 0 ≤ (438769 / 2 ^ 19 : ℚ)) ∧
    ((764999 / 2 ^ 20 : ℚ) + (857 / 2 ^ 60 : ℚ) ≤ (964863234815296345 / 2 ^ 60 : ℚ) ∧ (438769 / 2 ^ 19 : ℚ) + (857 / 2 ^ 60 : ℚ) ≤ (964863234815296345 / 2 ^ 60 : ℚ)) ∧
    ((764999 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 12 / 2 ^ 99 ≤ (857 / 2 ^ 60 : ℚ) ∧ (438769 / 2 ^ 19 : ℚ) / 2 ^ 50 + 2 ^ 12 / 2 ^ 99 ≤ (857 / 2 ^ 60 : ℚ)) ∧
    ((964863234815296345 / 2 ^ 60 : ℚ) ≤ (964863234815296345 / 2 ^ 60 : ℚ) ∧ (964863234815296345 / 2 ^ 60 : ℚ) ≤ (964863234815296345 / 2 ^ 60 : ℚ)) ∧
    ((812174517 / 2 ^ 20 : ℚ) ≤ 2 * (703072271 / 2 ^ 20 : ℚ)) ∧
    ((10774549 / 2 ^ 17 : ℚ) ≤ (703072271 / 2 ^ 20 : ℚ)) ∧
    ((E8).getD (18 - 1) 0 ≤ (703072271 / 2 ^ 20 : ℚ) / 2 ^ 70) ∧
    ((L8).getD (18 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((812174517 / 2 ^ 20 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (703072271 / 2 ^ 20 : ℚ)) ∧
    (0 < (703072271 / 2 ^ 20 : ℚ) ∧ ((703072271 / 2 ^ 20 : ℚ) ≤ (703072271 / 2 ^ 20 : ℚ) ∧ (812174517 / 2 ^ 20 : ℚ) ≤ (812174517 / 2 ^ 20 : ℚ))) := by
  decide +kernel

/-! ### Range 9: `(-7 : ℚ) < x < (-13 / 2 : ℚ)`, offset 561 -/

def C9 : List ℚ := LgammaPolyIv.pz [-13, -10, -8, -6, -4, -2, 0, 2, 4, 6, 8, 10, 11, 13, 15, 17, 19, 20, 22]
def Cl9 : List ℚ := LgammaPolyIv.pz [41, 44, 47, 48, 51, 52, 54, 59, 58, 65, 62, 66, 65, 69, 69, 71, 74, 75, 78]
def E9 : List ℚ := LgammaPolyIv.pz [74, 73, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72]
def L9 : List ℚ := LgammaPolyIv.pz [24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24]
def K9 : List ℚ := LgammaPolyIv.pz [21, 20, 18, 17, 15, 13, 11, 9, 7, 6, 4, 2, 0, -2, -4, -6, -8, -10]

theorem rok9 : LgammaRootEval.rootIvOk tab 564 19 6 1 (282809 / 2 ^ 19 : ℚ) (1895 / 2 ^ 12 : ℚ) (621903567879406121 / 2 ^ 60 : ℚ) (553 / 2 ^ 60 : ℚ) C9 Cl9 E9 L9 K9 = true := by
  decide +kernel

theorem tok9 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 602 6 (6 - 1)) (621903567879406121 / 2 ^ 60 : ℚ) = true := by
  decide +kernel

theorem tl9 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (621903567879406121 / 2 ^ 60 : ℚ) (0 :: LgammaRootPath.tailList tab 602 6) ≤ (9 / 2 ^ 27 : ℚ) := by
  decide +kernel

theorem rp9 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 564 19) (19 + 6) 1 (282809 / 2 ^ 19 : ℚ) (-5696287575 / 2 ^ 20 : ℚ) (-4842480811 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem rn9 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 564 19) (19 + 6) 1 (1895 / 2 ^ 12 : ℚ) (-5696287575 / 2 ^ 20 : ℚ) (-4842480811 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem lp9 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 564 19 ++ LgammaApprox.coeffs tab 602 2 6) ≤ (82240587 / 2 ^ 16 : ℚ) := by
  decide +kernel

theorem num9 :
    ((621903567879406121 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 602 6 (621903567879406121 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 602 6 (621903567879406121 / 2 ^ 60 : ℚ)) ≤ 1) ∧
    ((621903567879406121 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 602 6 (621903567879406121 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 602 6 (621903567879406121 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[564 + 2 * (19 - 1)]!)) ∧
    (((621903567879406121 / 2 ^ 60 : ℚ) * LgammaRootPath.tE tab 602 6 (621903567879406121 / 2 ^ 60 : ℚ) + (621903567879406121 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 602 6 (621903567879406121 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 602 6 (621903567879406121 / 2 ^ 60 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (9 / 2 ^ 27 : ℚ) * (553 / 2 ^ 60 : ℚ)) + ((621903567879406121 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 602 6 (621903567879406121 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 602 6 (621903567879406121 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl9).getD (19 - 1) 0) / 2 ^ 53 ≤ (E9).getD 0 0) ∧
    (((621903567879406121 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 602 6 (621903567879406121 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 602 6 (621903567879406121 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl9).getD (19 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L9).getD 0 0) ∧
    (2 ^ 2 ≤ LgammaApprox.q tab 561) ∧
    (PolyBound.qabs (LgammaApprox.q tab (561 + 1)) ≤ 2 ^ 2 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (561 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 2 ≤ -(-16140367457017414179 / 2 ^ 61 : ℚ)) ∧
    (-(-64562033938016094547 / 2 ^ 63 : ℚ) < 2 ^ (2 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 561 + (-64562033938016094547 / 2 ^ 63 : ℚ)) ∧
    (LgammaApprox.q tab 561 + (-16140367457017414179 / 2 ^ 61 : ℚ) ≤ 1 / 2) ∧
    (-(1895 / 2 ^ 12 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 14 * ((-64562033938016094547 / 2 ^ 63 : ℚ) + LgammaApprox.rootX0 561)) ∧
    (2 ^ 14 * ((-16140367457017414179 / 2 ^ 61 : ℚ) + LgammaApprox.rootX0 561) ≤ (282809 / 2 ^ 19 : ℚ) - 1 / 2 ^ 40) ∧
    ((282809 / 2 ^ 19 : ℚ) ≤ 1 ∧ (1895 / 2 ^ 12 : ℚ) ≤ 1 ∧ 0 ≤ (282809 / 2 ^ 19 : ℚ) ∧ 0 ≤ (1895 / 2 ^ 12 : ℚ)) ∧
    ((282809 / 2 ^ 19 : ℚ) + (553 / 2 ^ 60 : ℚ) ≤ (621903567879406121 / 2 ^ 60 : ℚ) ∧ (1895 / 2 ^ 12 : ℚ) + (553 / 2 ^ 60 : ℚ) ≤ (621903567879406121 / 2 ^ 60 : ℚ)) ∧
    ((282809 / 2 ^ 19 : ℚ) / 2 ^ 50 + 2 ^ 14 / 2 ^ 99 ≤ (553 / 2 ^ 60 : ℚ) ∧ (1895 / 2 ^ 12 : ℚ) / 2 ^ 50 + 2 ^ 14 / 2 ^ 99 ≤ (553 / 2 ^ 60 : ℚ)) ∧
    ((621903567879406121 / 2 ^ 60 : ℚ) ≤ (621903567879406121 / 2 ^ 60 : ℚ) ∧ (621903567879406121 / 2 ^ 60 : ℚ) ≤ (621903567879406121 / 2 ^ 60 : ℚ)) ∧
    ((5696287575 / 2 ^ 20 : ℚ) ≤ 2 * (4842480811 / 2 ^ 20 : ℚ)) ∧
    ((82240587 / 2 ^ 16 : ℚ) ≤ (4842480811 / 2 ^ 20 : ℚ)) ∧
    ((E9).getD (19 - 1) 0 ≤ (4842480811 / 2 ^ 20 : ℚ) / 2 ^ 70) ∧
    ((L9).getD (19 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((5696287575 / 2 ^ 20 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (4842480811 / 2 ^ 20 : ℚ)) ∧
    (0 < (4842480811 / 2 ^ 20 : ℚ) ∧ (-(5696287575 / 2 ^ 20 : ℚ) ≤ (-5696287575 / 2 ^ 20 : ℚ) ∧ (-4842480811 / 2 ^ 20 : ℚ) ≤ -(4842480811 / 2 ^ 20 : ℚ))) := by
  decide +kernel

/-! ### Range 10: `(-15 / 2 : ℚ) < x < (-7 : ℚ)`, offset 614 -/

def C10 : List ℚ := LgammaPolyIv.pz [-13, -9, -6, -3, 0, 3, 6, 9, 12, 15, 18, 20, 23, 26, 29, 32, 34, 37]
def Cl10 : List ℚ := LgammaPolyIv.pz [42, 45, 48, 53, 56, 58, 61, 64, 68, 69, 72, 74, 79, 81, 83, 86, 89, 93]
def E10 : List ℚ := LgammaPolyIv.pz [79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79, 79]
def L10 : List ℚ := LgammaPolyIv.pz [40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 39, 38, 36]
def K10 : List ℚ := LgammaPolyIv.pz [37, 34, 32, 29, 26, 23, 20, 17, 15, 12, 9, 6, 3, 0, -3, -6, -9]

theorem rok10 : LgammaRootEval.rootIvOk tab 617 18 6 1 (875841 / 2 ^ 20 : ℚ) (1004947 / 2 ^ 20 : ℚ) (552475455899304427 / 2 ^ 59 : ℚ) (491 / 2 ^ 59 : ℚ) C10 Cl10 E10 L10 K10 = true := by
  decide +kernel

theorem tok10 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 653 6 (6 - 1)) (552475455899304427 / 2 ^ 59 : ℚ) = true := by
  decide +kernel

theorem tl10 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (552475455899304427 / 2 ^ 59 : ℚ) (0 :: LgammaRootPath.tailList tab 653 6) ≤ (1 / 2 ^ 29 : ℚ) := by
  decide +kernel

theorem rp10 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 617 18) (18 + 6) 1 (875841 / 2 ^ 20 : ℚ) (76550345 / 2 ^ 14 : ℚ) (176907293 / 2 ^ 15 : ℚ) = true := by
  decide +kernel

theorem rn10 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 617 18) (18 + 6) 1 (1004947 / 2 ^ 20 : ℚ) (76550345 / 2 ^ 14 : ℚ) (176907293 / 2 ^ 15 : ℚ) = true := by
  decide +kernel

theorem lp10 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 617 18 ++ LgammaApprox.coeffs tab 653 2 6) ≤ (507467267 / 2 ^ 20 : ℚ) := by
  decide +kernel

theorem num10 :
    ((552475455899304427 / 2 ^ 59 : ℚ) * (LgammaRootPath.tM tab 653 6 (552475455899304427 / 2 ^ 59 : ℚ) + LgammaRootPath.tE tab 653 6 (552475455899304427 / 2 ^ 59 : ℚ)) ≤ 1) ∧
    ((552475455899304427 / 2 ^ 59 : ℚ) * (LgammaRootPath.tM tab 653 6 (552475455899304427 / 2 ^ 59 : ℚ) + LgammaRootPath.tE tab 653 6 (552475455899304427 / 2 ^ 59 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[617 + 2 * (18 - 1)]!)) ∧
    (((552475455899304427 / 2 ^ 59 : ℚ) * LgammaRootPath.tE tab 653 6 (552475455899304427 / 2 ^ 59 : ℚ) + (552475455899304427 / 2 ^ 59 : ℚ) * (LgammaRootPath.tM tab 653 6 (552475455899304427 / 2 ^ 59 : ℚ) + LgammaRootPath.tE tab 653 6 (552475455899304427 / 2 ^ 59 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (1 / 2 ^ 29 : ℚ) * (491 / 2 ^ 59 : ℚ)) + ((552475455899304427 / 2 ^ 59 : ℚ) * (LgammaRootPath.tM tab 653 6 (552475455899304427 / 2 ^ 59 : ℚ) + LgammaRootPath.tE tab 653 6 (552475455899304427 / 2 ^ 59 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl10).getD (18 - 1) 0) / 2 ^ 53 ≤ (E10).getD 0 0) ∧
    (((552475455899304427 / 2 ^ 59 : ℚ) * (LgammaRootPath.tM tab 653 6 (552475455899304427 / 2 ^ 59 : ℚ) + LgammaRootPath.tE tab 653 6 (552475455899304427 / 2 ^ 59 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl10).getD (18 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L10).getD 0 0) ∧
    (2 ^ 2 ≤ LgammaApprox.q tab 614) ∧
    (PolyBound.qabs (LgammaApprox.q tab (614 + 1)) ≤ 2 ^ 2 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (614 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 2 ≤ -(-129130396908495050053 / 2 ^ 64 : ℚ)) ∧
    (-(-64565703324134954215 / 2 ^ 63 : ℚ) < 2 ^ (2 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 614 + (-64565703324134954215 / 2 ^ 63 : ℚ)) ∧
    (LgammaApprox.q tab 614 + (-129130396908495050053 / 2 ^ 64 : ℚ) ≤ 1 / 2) ∧
    (-(1004947 / 2 ^ 20 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 15 * ((-64565703324134954215 / 2 ^ 63 : ℚ) + LgammaApprox.rootX0 614)) ∧
    (2 ^ 15 * ((-129130396908495050053 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 614) ≤ (875841 / 2 ^ 20 : ℚ) - 1 / 2 ^ 40) ∧
    ((875841 / 2 ^ 20 : ℚ) ≤ 1 ∧ (1004947 / 2 ^ 20 : ℚ) ≤ 1 ∧ 0 ≤ (875841 / 2 ^ 20 : ℚ) ∧ 0 ≤ (1004947 / 2 ^ 20 : ℚ)) ∧
    ((875841 / 2 ^ 20 : ℚ) + (491 / 2 ^ 59 : ℚ) ≤ (552475455899304427 / 2 ^ 59 : ℚ) ∧ (1004947 / 2 ^ 20 : ℚ) + (491 / 2 ^ 59 : ℚ) ≤ (552475455899304427 / 2 ^ 59 : ℚ)) ∧
    ((875841 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 15 / 2 ^ 99 ≤ (491 / 2 ^ 59 : ℚ) ∧ (1004947 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 15 / 2 ^ 99 ≤ (491 / 2 ^ 59 : ℚ)) ∧
    ((552475455899304427 / 2 ^ 59 : ℚ) ≤ (552475455899304427 / 2 ^ 59 : ℚ) ∧ (552475455899304427 / 2 ^ 59 : ℚ) ≤ (552475455899304427 / 2 ^ 59 : ℚ)) ∧
    ((176907293 / 2 ^ 15 : ℚ) ≤ 2 * (76550345 / 2 ^ 14 : ℚ)) ∧
    ((507467267 / 2 ^ 20 : ℚ) ≤ (76550345 / 2 ^ 14 : ℚ)) ∧
    ((E10).getD (18 - 1) 0 ≤ (76550345 / 2 ^ 14 : ℚ) / 2 ^ 70) ∧
    ((L10).getD (18 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((176907293 / 2 ^ 15 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (76550345 / 2 ^ 14 : ℚ)) ∧
    (0 < (76550345 / 2 ^ 14 : ℚ) ∧ ((76550345 / 2 ^ 14 : ℚ) ≤ (76550345 / 2 ^ 14 : ℚ) ∧ (176907293 / 2 ^ 15 : ℚ) ≤ (176907293 / 2 ^ 15 : ℚ))) := by
  decide +kernel

/-! ### Range 11: `(-8 : ℚ) < x < (-15 / 2 : ℚ)`, offset 665 -/

def C11 : List ℚ := LgammaPolyIv.pz [-16, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 6, 8, 10, 12, 14, 16, 17, 19, 21, 23]
def Cl11 : List ℚ := LgammaPolyIv.pz [39, 41, 43, 47, 49, 50, 52, 57, 55, 57, 61, 60, 63, 66, 68, 68, 70, 71, 75, 78, 77]
def E11 : List ℚ := LgammaPolyIv.pz [74, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73]
def L11 : List ℚ := LgammaPolyIv.pz [25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25]
def K11 : List ℚ := LgammaPolyIv.pz [22, 20, 19, 17, 15, 13, 12, 10, 8, 6, 4, 3, 1, -1, -3, -5, -7, -9, -11, -13]

theorem rok11 : LgammaRootEval.rootIvOk tab 668 21 6 1 (349705 / 2 ^ 19 : ℚ) (580335 / 2 ^ 20 : ℚ) (192252356895703211 / 2 ^ 58 : ℚ) (171 / 2 ^ 58 : ℚ) C11 Cl11 E11 L11 K11 = true := by
  decide +kernel

theorem tok11 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 710 6 (6 - 1)) (192252356895703211 / 2 ^ 58 : ℚ) = true := by
  decide +kernel

theorem tl11 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (192252356895703211 / 2 ^ 58 : ℚ) (0 :: LgammaRootPath.tailList tab 710 6) ≤ (55 / 2 ^ 30 : ℚ) := by
  decide +kernel

theorem rp11 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 668 21) (21 + 6) 1 (349705 / 2 ^ 19 : ℚ) (-46341548785 / 2 ^ 20 : ℚ) (-18968560309 / 2 ^ 19 : ℚ) = true := by
  decide +kernel

theorem rn11 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 668 21) (21 + 6) 1 (580335 / 2 ^ 20 : ℚ) (-46341548785 / 2 ^ 20 : ℚ) (-18968560309 / 2 ^ 19 : ℚ) = true := by
  decide +kernel

theorem lp11 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 668 21 ++ LgammaApprox.coeffs tab 710 2 6) ≤ (5268101779 / 2 ^ 19 : ℚ) := by
  decide +kernel

theorem num11 :
    ((192252356895703211 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 710 6 (192252356895703211 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 710 6 (192252356895703211 / 2 ^ 58 : ℚ)) ≤ 1) ∧
    ((192252356895703211 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 710 6 (192252356895703211 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 710 6 (192252356895703211 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[668 + 2 * (21 - 1)]!)) ∧
    (((192252356895703211 / 2 ^ 58 : ℚ) * LgammaRootPath.tE tab 710 6 (192252356895703211 / 2 ^ 58 : ℚ) + (192252356895703211 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 710 6 (192252356895703211 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 710 6 (192252356895703211 / 2 ^ 58 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (55 / 2 ^ 30 : ℚ) * (171 / 2 ^ 58 : ℚ)) + ((192252356895703211 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 710 6 (192252356895703211 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 710 6 (192252356895703211 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl11).getD (21 - 1) 0) / 2 ^ 53 ≤ (E11).getD 0 0) ∧
    (((192252356895703211 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 710 6 (192252356895703211 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 710 6 (192252356895703211 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl11).getD (21 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L11).getD 0 0) ∧
    (2 ^ 2 ≤ LgammaApprox.q tab 665) ∧
    (PolyBound.qabs (LgammaApprox.q tab (665 + 1)) ≤ 2 ^ 2 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (665 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 2 ≤ -(-147573401183629697185 / 2 ^ 64 : ℚ)) ∧
    (-(-73786786474037282047 / 2 ^ 63 : ℚ) < 2 ^ (2 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 665 + (-73786786474037282047 / 2 ^ 63 : ℚ)) ∧
    (LgammaApprox.q tab 665 + (-147573401183629697185 / 2 ^ 64 : ℚ) ≤ 1 / 2) ∧
    (-(580335 / 2 ^ 20 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 17 * ((-73786786474037282047 / 2 ^ 63 : ℚ) + LgammaApprox.rootX0 665)) ∧
    (2 ^ 17 * ((-147573401183629697185 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 665) ≤ (349705 / 2 ^ 19 : ℚ) - 1 / 2 ^ 40) ∧
    ((349705 / 2 ^ 19 : ℚ) ≤ 1 ∧ (580335 / 2 ^ 20 : ℚ) ≤ 1 ∧ 0 ≤ (349705 / 2 ^ 19 : ℚ) ∧ 0 ≤ (580335 / 2 ^ 20 : ℚ)) ∧
    ((349705 / 2 ^ 19 : ℚ) + (171 / 2 ^ 58 : ℚ) ≤ (192252356895703211 / 2 ^ 58 : ℚ) ∧ (580335 / 2 ^ 20 : ℚ) + (171 / 2 ^ 58 : ℚ) ≤ (192252356895703211 / 2 ^ 58 : ℚ)) ∧
    ((349705 / 2 ^ 19 : ℚ) / 2 ^ 50 + 2 ^ 17 / 2 ^ 99 ≤ (171 / 2 ^ 58 : ℚ) ∧ (580335 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 17 / 2 ^ 99 ≤ (171 / 2 ^ 58 : ℚ)) ∧
    ((192252356895703211 / 2 ^ 58 : ℚ) ≤ (192252356895703211 / 2 ^ 58 : ℚ) ∧ (192252356895703211 / 2 ^ 58 : ℚ) ≤ (192252356895703211 / 2 ^ 58 : ℚ)) ∧
    ((46341548785 / 2 ^ 20 : ℚ) ≤ 2 * (18968560309 / 2 ^ 19 : ℚ)) ∧
    ((5268101779 / 2 ^ 19 : ℚ) ≤ (18968560309 / 2 ^ 19 : ℚ)) ∧
    ((E11).getD (21 - 1) 0 ≤ (18968560309 / 2 ^ 19 : ℚ) / 2 ^ 70) ∧
    ((L11).getD (21 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((46341548785 / 2 ^ 20 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (18968560309 / 2 ^ 19 : ℚ)) ∧
    (0 < (18968560309 / 2 ^ 19 : ℚ) ∧ (-(46341548785 / 2 ^ 20 : ℚ) ≤ (-46341548785 / 2 ^ 20 : ℚ) ∧ (-18968560309 / 2 ^ 19 : ℚ) ≤ -(18968560309 / 2 ^ 19 : ℚ))) := by
  decide +kernel

/-! ### Range 12: `(-17 / 2 : ℚ) < x < (-8 : ℚ)`, offset 722 -/

def C12 : List ℚ := LgammaPolyIv.pz [-16, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 6, 8, 10, 12, 14, 15, 17, 19, 21, 23]
def Cl12 : List ℚ := LgammaPolyIv.pz [38, 41, 43, 48, 47, 54, 51, 54, 58, 57, 61, 60, 63, 65, 66, 68, 69, 73, 73, 75, 79]
def E12 : List ℚ := LgammaPolyIv.pz [74, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73, 73]
def L12 : List ℚ := LgammaPolyIv.pz [25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25]
def K12 : List ℚ := LgammaPolyIv.pz [22, 20, 19, 17, 15, 13, 12, 10, 8, 6, 4, 3, 1, -1, -3, -5, -7, -9, -11, -13]

theorem rok12 : LgammaRootEval.rootIvOk tab 725 21 6 1 (580311 / 2 ^ 20 : ℚ) (699375 / 2 ^ 20 : ℚ) (768970944675840683 / 2 ^ 60 : ℚ) (683 / 2 ^ 60 : ℚ) C12 Cl12 E12 L12 K12 = true := by
  decide +kernel

theorem tok12 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 767 6 (6 - 1)) (768970944675840683 / 2 ^ 60 : ℚ) = true := by
  decide +kernel

theorem tl12 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (768970944675840683 / 2 ^ 60 : ℚ) (0 :: LgammaRootPath.tailList tab 767 6) ≤ (7 / 2 ^ 27 : ℚ) := by
  decide +kernel

theorem rp12 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 725 21) (21 + 6) 1 (580311 / 2 ^ 20 : ℚ) (9486348769 / 2 ^ 18 : ℚ) (23175628931 / 2 ^ 19 : ℚ) = true := by
  decide +kernel

theorem rn12 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 725 21) (21 + 6) 1 (699375 / 2 ^ 20 : ℚ) (9486348769 / 2 ^ 18 : ℚ) (23175628931 / 2 ^ 19 : ℚ) = true := by
  decide +kernel

theorem lp12 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 725 21 ++ LgammaApprox.coeffs tab 767 2 6) ≤ (10539084217 / 2 ^ 20 : ℚ) := by
  decide +kernel

theorem num12 :
    ((768970944675840683 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 767 6 (768970944675840683 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 767 6 (768970944675840683 / 2 ^ 60 : ℚ)) ≤ 1) ∧
    ((768970944675840683 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 767 6 (768970944675840683 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 767 6 (768970944675840683 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[725 + 2 * (21 - 1)]!)) ∧
    (((768970944675840683 / 2 ^ 60 : ℚ) * LgammaRootPath.tE tab 767 6 (768970944675840683 / 2 ^ 60 : ℚ) + (768970944675840683 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 767 6 (768970944675840683 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 767 6 (768970944675840683 / 2 ^ 60 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (7 / 2 ^ 27 : ℚ) * (683 / 2 ^ 60 : ℚ)) + ((768970944675840683 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 767 6 (768970944675840683 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 767 6 (768970944675840683 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl12).getD (21 - 1) 0) / 2 ^ 53 ≤ (E12).getD 0 0) ∧
    (((768970944675840683 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 767 6 (768970944675840683 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 767 6 (768970944675840683 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl12).getD (21 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L12).getD 0 0) ∧
    (2 ^ 3 ≤ LgammaApprox.q tab 722) ∧
    (PolyBound.qabs (LgammaApprox.q tab (722 + 1)) ≤ 2 ^ 3 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (722 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 3 ≤ -(-18446791523251882447 / 2 ^ 61 : ℚ)) ∧
    (-(-147574503942326973793 / 2 ^ 64 : ℚ) < 2 ^ (3 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 722 + (-147574503942326973793 / 2 ^ 64 : ℚ)) ∧
    (LgammaApprox.q tab 722 + (-18446791523251882447 / 2 ^ 61 : ℚ) ≤ 1 / 2) ∧
    (-(699375 / 2 ^ 20 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 17 * ((-147574503942326973793 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 722)) ∧
    (2 ^ 17 * ((-18446791523251882447 / 2 ^ 61 : ℚ) + LgammaApprox.rootX0 722) ≤ (580311 / 2 ^ 20 : ℚ) - 1 / 2 ^ 40) ∧
    ((580311 / 2 ^ 20 : ℚ) ≤ 1 ∧ (699375 / 2 ^ 20 : ℚ) ≤ 1 ∧ 0 ≤ (580311 / 2 ^ 20 : ℚ) ∧ 0 ≤ (699375 / 2 ^ 20 : ℚ)) ∧
    ((580311 / 2 ^ 20 : ℚ) + (683 / 2 ^ 60 : ℚ) ≤ (768970944675840683 / 2 ^ 60 : ℚ) ∧ (699375 / 2 ^ 20 : ℚ) + (683 / 2 ^ 60 : ℚ) ≤ (768970944675840683 / 2 ^ 60 : ℚ)) ∧
    ((580311 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 17 / 2 ^ 99 ≤ (683 / 2 ^ 60 : ℚ) ∧ (699375 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 17 / 2 ^ 99 ≤ (683 / 2 ^ 60 : ℚ)) ∧
    ((768970944675840683 / 2 ^ 60 : ℚ) ≤ (768970944675840683 / 2 ^ 60 : ℚ) ∧ (768970944675840683 / 2 ^ 60 : ℚ) ≤ (768970944675840683 / 2 ^ 60 : ℚ)) ∧
    ((23175628931 / 2 ^ 19 : ℚ) ≤ 2 * (9486348769 / 2 ^ 18 : ℚ)) ∧
    ((10539084217 / 2 ^ 20 : ℚ) ≤ (9486348769 / 2 ^ 18 : ℚ)) ∧
    ((E12).getD (21 - 1) 0 ≤ (9486348769 / 2 ^ 18 : ℚ) / 2 ^ 70) ∧
    ((L12).getD (21 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((23175628931 / 2 ^ 19 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (9486348769 / 2 ^ 18 : ℚ)) ∧
    (0 < (9486348769 / 2 ^ 18 : ℚ) ∧ ((9486348769 / 2 ^ 18 : ℚ) ≤ (9486348769 / 2 ^ 18 : ℚ) ∧ (23175628931 / 2 ^ 19 : ℚ) ≤ (23175628931 / 2 ^ 19 : ℚ))) := by
  decide +kernel

/-! ### Range 13: `(-9 : ℚ) < x < (-17 / 2 : ℚ)`, offset 779 -/

def C13 : List ℚ := LgammaPolyIv.pz [-19, -16, -14, -12, -11, -9, -7, -5, -4, -2, 0, 1, 3, 5, 6, 8, 10, 11, 13, 14, 16, 18]
def Cl13 : List ℚ := LgammaPolyIv.pz [36, 38, 40, 42, 44, 45, 48, 50, 50, 52, 55, 57, 58, 62, 61, 64, 64, 68, 67, 68, 72, 72]
def E13 : List ℚ := LgammaPolyIv.pz [69, 68, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67]
def L13 : List ℚ := LgammaPolyIv.pz [19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19]
def K13 : List ℚ := LgammaPolyIv.pz [17, 16, 14, 13, 11, 9, 8, 6, 4, 3, 1, 0, -2, -4, -6, -7, -9, -11, -13, -15, -17]

theorem rok13 : LgammaRootEval.rootIvOk tab 782 22 6 1 (342287 / 2 ^ 19 : ℚ) (279205 / 2 ^ 19 : ℚ) (752697073073128093 / 2 ^ 60 : ℚ) (669 / 2 ^ 60 : ℚ) C13 Cl13 E13 L13 K13 = true := by
  decide +kernel

theorem tok13 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 826 6 (6 - 1)) (752697073073128093 / 2 ^ 60 : ℚ) = true := by
  decide +kernel

theorem tl13 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (752697073073128093 / 2 ^ 60 : ℚ) (0 :: LgammaRootPath.tailList tab 826 6) ≤ (2007 / 2 ^ 30 : ℚ) := by
  decide +kernel

theorem rp13 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 782 22) (22 + 6) 1 (342287 / 2 ^ 19 : ℚ) (-210286144609 / 2 ^ 19 : ℚ) (-337518107029 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem rn13 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 782 22) (22 + 6) 1 (279205 / 2 ^ 19 : ℚ) (-210286144609 / 2 ^ 19 : ℚ) (-337518107029 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem lp13 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 782 22 ++ LgammaApprox.coeffs tab 826 2 6) ≤ (114853250817 / 2 ^ 20 : ℚ) := by
  decide +kernel

theorem num13 :
    ((752697073073128093 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 826 6 (752697073073128093 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 826 6 (752697073073128093 / 2 ^ 60 : ℚ)) ≤ 1) ∧
    ((752697073073128093 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 826 6 (752697073073128093 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 826 6 (752697073073128093 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[782 + 2 * (22 - 1)]!)) ∧
    (((752697073073128093 / 2 ^ 60 : ℚ) * LgammaRootPath.tE tab 826 6 (752697073073128093 / 2 ^ 60 : ℚ) + (752697073073128093 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 826 6 (752697073073128093 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 826 6 (752697073073128093 / 2 ^ 60 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (2007 / 2 ^ 30 : ℚ) * (669 / 2 ^ 60 : ℚ)) + ((752697073073128093 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 826 6 (752697073073128093 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 826 6 (752697073073128093 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl13).getD (22 - 1) 0) / 2 ^ 53 ≤ (E13).getD 0 0) ∧
    (((752697073073128093 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 826 6 (752697073073128093 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 826 6 (752697073073128093 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl13).getD (22 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L13).getD 0 0) ∧
    (2 ^ 3 ≤ LgammaApprox.q tab 779) ∧
    (PolyBound.qabs (LgammaApprox.q tab (779 + 1)) ≤ 2 ^ 3 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (779 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 3 ≤ -(-83010317171775948795 / 2 ^ 63 : ℚ)) ∧
    (-(-166020655197343035241 / 2 ^ 64 : ℚ) < 2 ^ (3 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 779 + (-166020655197343035241 / 2 ^ 64 : ℚ)) ∧
    (LgammaApprox.q tab 779 + (-83010317171775948795 / 2 ^ 63 : ℚ) ≤ 1 / 2) ∧
    (-(279205 / 2 ^ 19 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 20 * ((-166020655197343035241 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 779)) ∧
    (2 ^ 20 * ((-83010317171775948795 / 2 ^ 63 : ℚ) + LgammaApprox.rootX0 779) ≤ (342287 / 2 ^ 19 : ℚ) - 1 / 2 ^ 40) ∧
    ((342287 / 2 ^ 19 : ℚ) ≤ 1 ∧ (279205 / 2 ^ 19 : ℚ) ≤ 1 ∧ 0 ≤ (342287 / 2 ^ 19 : ℚ) ∧ 0 ≤ (279205 / 2 ^ 19 : ℚ)) ∧
    ((342287 / 2 ^ 19 : ℚ) + (669 / 2 ^ 60 : ℚ) ≤ (752697073073128093 / 2 ^ 60 : ℚ) ∧ (279205 / 2 ^ 19 : ℚ) + (669 / 2 ^ 60 : ℚ) ≤ (752697073073128093 / 2 ^ 60 : ℚ)) ∧
    ((342287 / 2 ^ 19 : ℚ) / 2 ^ 50 + 2 ^ 20 / 2 ^ 99 ≤ (669 / 2 ^ 60 : ℚ) ∧ (279205 / 2 ^ 19 : ℚ) / 2 ^ 50 + 2 ^ 20 / 2 ^ 99 ≤ (669 / 2 ^ 60 : ℚ)) ∧
    ((752697073073128093 / 2 ^ 60 : ℚ) ≤ (752697073073128093 / 2 ^ 60 : ℚ) ∧ (752697073073128093 / 2 ^ 60 : ℚ) ≤ (752697073073128093 / 2 ^ 60 : ℚ)) ∧
    ((210286144609 / 2 ^ 19 : ℚ) ≤ 2 * (337518107029 / 2 ^ 20 : ℚ)) ∧
    ((114853250817 / 2 ^ 20 : ℚ) ≤ (337518107029 / 2 ^ 20 : ℚ)) ∧
    ((E13).getD (22 - 1) 0 ≤ (337518107029 / 2 ^ 20 : ℚ) / 2 ^ 70) ∧
    ((L13).getD (22 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((210286144609 / 2 ^ 19 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (337518107029 / 2 ^ 20 : ℚ)) ∧
    (0 < (337518107029 / 2 ^ 20 : ℚ) ∧ (-(210286144609 / 2 ^ 19 : ℚ) ≤ (-210286144609 / 2 ^ 19 : ℚ) ∧ (-337518107029 / 2 ^ 20 : ℚ) ≤ -(337518107029 / 2 ^ 20 : ℚ))) := by
  decide +kernel

/-! ### Range 14: `(-19 / 2 : ℚ) < x < (-9 : ℚ)`, offset 838 -/

def C14 : List ℚ := LgammaPolyIv.pz [-19, -16, -14, -12, -11, -9, -7, -5, -4, -2, 0, 1, 3, 5, 6, 8, 10, 11, 13, 14, 16, 18]
def Cl14 : List ℚ := LgammaPolyIv.pz [37, 38, 41, 42, 43, 45, 47, 49, 50, 53, 54, 55, 57, 59, 60, 62, 64, 65, 67, 68, 70, 74]
def E14 : List ℚ := LgammaPolyIv.pz [69, 68, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67, 67]
def L14 : List ℚ := LgammaPolyIv.pz [19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19]
def K14 : List ℚ := LgammaPolyIv.pz [17, 16, 14, 13, 11, 9, 8, 6, 4, 3, 1, 0, -2, -4, -6, -7, -9, -11, -13, -15, -17]

theorem rok14 : LgammaRootEval.rootIvOk tab 841 22 6 1 (558397 / 2 ^ 20 : ℚ) (684555 / 2 ^ 20 : ℚ) (752676182352200349 / 2 ^ 60 : ℚ) (669 / 2 ^ 60 : ℚ) C14 Cl14 E14 L14 K14 = true := by
  decide +kernel

theorem tok14 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 885 6 (6 - 1)) (752676182352200349 / 2 ^ 60 : ℚ) = true := by
  decide +kernel

theorem tl14 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (752676182352200349 / 2 ^ 60 : ℚ) (0 :: LgammaRootPath.tailList tab 885 6) ≤ (251 / 2 ^ 27 : ℚ) := by
  decide +kernel

theorem rp14 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 841 22) (22 + 6) 1 (558397 / 2 ^ 20 : ℚ) (337527677679 / 2 ^ 20 : ℚ) (420581732105 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem rn14 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 841 22) (22 + 6) 1 (684555 / 2 ^ 20 : ℚ) (337527677679 / 2 ^ 20 : ℚ) (420581732105 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem lp14 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 841 22 ++ LgammaApprox.coeffs tab 885 2 6) ≤ (57428536231 / 2 ^ 19 : ℚ) := by
  decide +kernel

theorem num14 :
    ((752676182352200349 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 885 6 (752676182352200349 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 885 6 (752676182352200349 / 2 ^ 60 : ℚ)) ≤ 1) ∧
    ((752676182352200349 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 885 6 (752676182352200349 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 885 6 (752676182352200349 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[841 + 2 * (22 - 1)]!)) ∧
    (((752676182352200349 / 2 ^ 60 : ℚ) * LgammaRootPath.tE tab 885 6 (752676182352200349 / 2 ^ 60 : ℚ) + (752676182352200349 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 885 6 (752676182352200349 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 885 6 (752676182352200349 / 2 ^ 60 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (251 / 2 ^ 27 : ℚ) * (669 / 2 ^ 60 : ℚ)) + ((752676182352200349 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 885 6 (752676182352200349 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 885 6 (752676182352200349 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl14).getD (22 - 1) 0) / 2 ^ 53 ≤ (E14).getD 0 0) ∧
    (((752676182352200349 / 2 ^ 60 : ℚ) * (LgammaRootPath.tM tab 885 6 (752676182352200349 / 2 ^ 60 : ℚ) + LgammaRootPath.tE tab 885 6 (752676182352200349 / 2 ^ 60 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl14).getD (22 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L14).getD 0 0) ∧
    (2 ^ 3 ≤ LgammaApprox.q tab 838) ∧
    (PolyBound.qabs (LgammaApprox.q tab (838 + 1)) ≤ 2 ^ 3 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (838 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 3 ≤ -(-83010369064504561761 / 2 ^ 63 : ℚ)) ∧
    (-(-166020758982271881795 / 2 ^ 64 : ℚ) < 2 ^ (3 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 838 + (-166020758982271881795 / 2 ^ 64 : ℚ)) ∧
    (LgammaApprox.q tab 838 + (-83010369064504561761 / 2 ^ 63 : ℚ) ≤ 1 / 2) ∧
    (-(684555 / 2 ^ 20 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 20 * ((-166020758982271881795 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 838)) ∧
    (2 ^ 20 * ((-83010369064504561761 / 2 ^ 63 : ℚ) + LgammaApprox.rootX0 838) ≤ (558397 / 2 ^ 20 : ℚ) - 1 / 2 ^ 40) ∧
    ((558397 / 2 ^ 20 : ℚ) ≤ 1 ∧ (684555 / 2 ^ 20 : ℚ) ≤ 1 ∧ 0 ≤ (558397 / 2 ^ 20 : ℚ) ∧ 0 ≤ (684555 / 2 ^ 20 : ℚ)) ∧
    ((558397 / 2 ^ 20 : ℚ) + (669 / 2 ^ 60 : ℚ) ≤ (752676182352200349 / 2 ^ 60 : ℚ) ∧ (684555 / 2 ^ 20 : ℚ) + (669 / 2 ^ 60 : ℚ) ≤ (752676182352200349 / 2 ^ 60 : ℚ)) ∧
    ((558397 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 20 / 2 ^ 99 ≤ (669 / 2 ^ 60 : ℚ) ∧ (684555 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 20 / 2 ^ 99 ≤ (669 / 2 ^ 60 : ℚ)) ∧
    ((752676182352200349 / 2 ^ 60 : ℚ) ≤ (752676182352200349 / 2 ^ 60 : ℚ) ∧ (752676182352200349 / 2 ^ 60 : ℚ) ≤ (752676182352200349 / 2 ^ 60 : ℚ)) ∧
    ((420581732105 / 2 ^ 20 : ℚ) ≤ 2 * (337527677679 / 2 ^ 20 : ℚ)) ∧
    ((57428536231 / 2 ^ 19 : ℚ) ≤ (337527677679 / 2 ^ 20 : ℚ)) ∧
    ((E14).getD (22 - 1) 0 ≤ (337527677679 / 2 ^ 20 : ℚ) / 2 ^ 70) ∧
    ((L14).getD (22 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((420581732105 / 2 ^ 20 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (337527677679 / 2 ^ 20 : ℚ)) ∧
    (0 < (337527677679 / 2 ^ 20 : ℚ) ∧ ((337527677679 / 2 ^ 20 : ℚ) ≤ (337527677679 / 2 ^ 20 : ℚ) ∧ (420581732105 / 2 ^ 20 : ℚ) ≤ (420581732105 / 2 ^ 20 : ℚ))) := by
  decide +kernel

/-! ### Range 15: `(-10 : ℚ) < x < (-19 / 2 : ℚ)`, offset 897 -/

def C15 : List ℚ := LgammaPolyIv.pz [-22, -19, -16, -14, -11, -9, -6, -4, -1, 1, 3, 6, 8, 10, 13, 15, 17, 19, 22, 24, 26]
def Cl15 : List ℚ := LgammaPolyIv.pz [32, 35, 38, 40, 45, 47, 50, 50, 54, 56, 61, 60, 62, 65, 73, 69, 73, 73, 76, 78, 80]
def E15 : List ℚ := LgammaPolyIv.pz [77, 76, 75, 74, 73, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 71]
def L15 : List ℚ := LgammaPolyIv.pz [28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 27, 26]
def K15 : List ℚ := LgammaPolyIv.pz [26, 24, 21, 19, 17, 15, 12, 10, 8, 5, 3, 1, -2, -4, -6, -9, -11, -14, -16, -19]

theorem rok15 : LgammaRootEval.rootIvOk tab 900 21 6 1 (497301 / 2 ^ 19 : ℚ) (412643 / 2 ^ 19 : ℚ) (273394116002316531 / 2 ^ 58 : ℚ) (243 / 2 ^ 58 : ℚ) C15 Cl15 E15 L15 K15 = true := by
  decide +kernel

theorem tok15 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 942 6 (6 - 1)) (273394116002316531 / 2 ^ 58 : ℚ) = true := by
  decide +kernel

theorem tl15 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (273394116002316531 / 2 ^ 58 : ℚ) (0 :: LgammaRootPath.tailList tab 942 6) ≤ (1 / 2 ^ 28 : ℚ) := by
  decide +kernel

theorem rp15 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 900 21) (21 + 6) 1 (497301 / 2 ^ 19 : ℚ) (-4171139599115 / 2 ^ 20 : ℚ) (-853685985271 / 2 ^ 18 : ℚ) = true := by
  decide +kernel

theorem rn15 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 900 21) (21 + 6) 1 (412643 / 2 ^ 19 : ℚ) (-4171139599115 / 2 ^ 20 : ℚ) (-853685985271 / 2 ^ 18 : ℚ) = true := by
  decide +kernel

theorem lp15 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 900 21 ++ LgammaApprox.coeffs tab 942 2 6) ≤ (567648603245 / 2 ^ 20 : ℚ) := by
  decide +kernel

theorem num15 :
    ((273394116002316531 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 942 6 (273394116002316531 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 942 6 (273394116002316531 / 2 ^ 58 : ℚ)) ≤ 1) ∧
    ((273394116002316531 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 942 6 (273394116002316531 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 942 6 (273394116002316531 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[900 + 2 * (21 - 1)]!)) ∧
    (((273394116002316531 / 2 ^ 58 : ℚ) * LgammaRootPath.tE tab 942 6 (273394116002316531 / 2 ^ 58 : ℚ) + (273394116002316531 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 942 6 (273394116002316531 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 942 6 (273394116002316531 / 2 ^ 58 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (1 / 2 ^ 28 : ℚ) * (243 / 2 ^ 58 : ℚ)) + ((273394116002316531 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 942 6 (273394116002316531 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 942 6 (273394116002316531 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl15).getD (21 - 1) 0) / 2 ^ 53 ≤ (E15).getD 0 0) ∧
    (((273394116002316531 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 942 6 (273394116002316531 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 942 6 (273394116002316531 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl15).getD (21 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L15).getD 0 0) ∧
    (2 ^ 3 ≤ LgammaApprox.q tab 897) ∧
    (PolyBound.qabs (LgammaApprox.q tab (897 + 1)) ≤ 2 ^ 3 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (897 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 3 ≤ -(-184467434610748909899 / 2 ^ 64 : ℚ)) ∧
    (-(-184467436519039061843 / 2 ^ 64 : ℚ) < 2 ^ (3 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 897 + (-184467436519039061843 / 2 ^ 64 : ℚ)) ∧
    (LgammaApprox.q tab 897 + (-184467434610748909899 / 2 ^ 64 : ℚ) ≤ 1 / 2) ∧
    (-(412643 / 2 ^ 19 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 24 * ((-184467436519039061843 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 897)) ∧
    (2 ^ 24 * ((-184467434610748909899 / 2 ^ 64 : ℚ) + LgammaApprox.rootX0 897) ≤ (497301 / 2 ^ 19 : ℚ) - 1 / 2 ^ 40) ∧
    ((497301 / 2 ^ 19 : ℚ) ≤ 1 ∧ (412643 / 2 ^ 19 : ℚ) ≤ 1 ∧ 0 ≤ (497301 / 2 ^ 19 : ℚ) ∧ 0 ≤ (412643 / 2 ^ 19 : ℚ)) ∧
    ((497301 / 2 ^ 19 : ℚ) + (243 / 2 ^ 58 : ℚ) ≤ (273394116002316531 / 2 ^ 58 : ℚ) ∧ (412643 / 2 ^ 19 : ℚ) + (243 / 2 ^ 58 : ℚ) ≤ (273394116002316531 / 2 ^ 58 : ℚ)) ∧
    ((497301 / 2 ^ 19 : ℚ) / 2 ^ 50 + 2 ^ 24 / 2 ^ 99 ≤ (243 / 2 ^ 58 : ℚ) ∧ (412643 / 2 ^ 19 : ℚ) / 2 ^ 50 + 2 ^ 24 / 2 ^ 99 ≤ (243 / 2 ^ 58 : ℚ)) ∧
    ((273394116002316531 / 2 ^ 58 : ℚ) ≤ (273394116002316531 / 2 ^ 58 : ℚ) ∧ (273394116002316531 / 2 ^ 58 : ℚ) ≤ (273394116002316531 / 2 ^ 58 : ℚ)) ∧
    ((4171139599115 / 2 ^ 20 : ℚ) ≤ 2 * (853685985271 / 2 ^ 18 : ℚ)) ∧
    ((567648603245 / 2 ^ 20 : ℚ) ≤ (853685985271 / 2 ^ 18 : ℚ)) ∧
    ((E15).getD (21 - 1) 0 ≤ (853685985271 / 2 ^ 18 : ℚ) / 2 ^ 70) ∧
    ((L15).getD (21 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((4171139599115 / 2 ^ 20 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (853685985271 / 2 ^ 18 : ℚ)) ∧
    (0 < (853685985271 / 2 ^ 18 : ℚ) ∧ (-(4171139599115 / 2 ^ 20 : ℚ) ≤ (-4171139599115 / 2 ^ 20 : ℚ) ∧ (-853685985271 / 2 ^ 18 : ℚ) ≤ -(853685985271 / 2 ^ 18 : ℚ))) := by
  decide +kernel

/-! ### Range 16: `(-21 / 2 : ℚ) < x < (-10 : ℚ)`, offset 954 -/

def C16 : List ℚ := LgammaPolyIv.pz [-22, -19, -16, -14, -11, -9, -6, -4, -1, 1, 3, 6, 8, 10, 13, 15, 17, 19, 22, 24, 26]
def Cl16 : List ℚ := LgammaPolyIv.pz [34, 35, 38, 40, 46, 45, 48, 50, 53, 55, 57, 61, 62, 64, 69, 69, 71, 74, 82, 79, 81]
def E16 : List ℚ := LgammaPolyIv.pz [77, 76, 75, 74, 73, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 72, 71]
def L16 : List ℚ := LgammaPolyIv.pz [28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 27, 26]
def K16 : List ℚ := LgammaPolyIv.pz [26, 24, 21, 19, 17, 15, 12, 10, 8, 5, 3, 1, -2, -4, -6, -9, -11, -14, -16, -19]

theorem rok16 : LgammaRootEval.rootIvOk tab 957 21 6 1 (206321 / 2 ^ 18 : ℚ) (994599 / 2 ^ 20 : ℚ) (273393291368595699 / 2 ^ 58 : ℚ) (243 / 2 ^ 58 : ℚ) C16 Cl16 E16 L16 K16 = true := by
  decide +kernel

theorem tok16 : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab 999 6 (6 - 1)) (273393291368595699 / 2 ^ 58 : ℚ) = true := by
  decide +kernel

theorem tl16 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ (273393291368595699 / 2 ^ 58 : ℚ) (0 :: LgammaRootPath.tailList tab 999 6) ≤ (1 / 2 ^ 28 : ℚ) := by
  decide +kernel

theorem rp16 : LgammaRootEval.rangeOk (LgammaRootEval.cf tab 957 21) (21 + 6) 1 (206321 / 2 ^ 18 : ℚ) (1707376985267 / 2 ^ 19 : ℚ) (4171149470241 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem rn16 : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab 957 21) (21 + 6) 1 (994599 / 2 ^ 20 : ℚ) (1707376985267 / 2 ^ 19 : ℚ) (4171149470241 / 2 ^ 20 : ℚ) = true := by
  decide +kernel

theorem lp16 : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab 957 21 ++ LgammaApprox.coeffs tab 999 2 6) ≤ (141912585019 / 2 ^ 18 : ℚ) := by
  decide +kernel

theorem num16 :
    ((273393291368595699 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 999 6 (273393291368595699 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 999 6 (273393291368595699 / 2 ^ 58 : ℚ)) ≤ 1) ∧
    ((273393291368595699 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 999 6 (273393291368595699 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 999 6 (273393291368595699 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[957 + 2 * (21 - 1)]!)) ∧
    (((273393291368595699 / 2 ^ 58 : ℚ) * LgammaRootPath.tE tab 999 6 (273393291368595699 / 2 ^ 58 : ℚ) + (273393291368595699 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 999 6 (273393291368595699 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 999 6 (273393291368595699 / 2 ^ 58 : ℚ)) / 2 ^ 53 + 1 / 2 ^ 1075 + (1 / 2 ^ 28 : ℚ) * (243 / 2 ^ 58 : ℚ)) + ((273393291368595699 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 999 6 (273393291368595699 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 999 6 (273393291368595699 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl16).getD (21 - 1) 0) / 2 ^ 53 ≤ (E16).getD 0 0) ∧
    (((273393291368595699 / 2 ^ 58 : ℚ) * (LgammaRootPath.tM tab 999 6 (273393291368595699 / 2 ^ 58 : ℚ) + LgammaRootPath.tE tab 999 6 (273393291368595699 / 2 ^ 58 : ℚ)) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + (Cl16).getD (21 - 1) 0) * (1 + 1 / 2 ^ 53) ≤ (L16).getD 0 0) ∧
    (2 ^ 3 ≤ LgammaApprox.q tab 954) ∧
    (PolyBound.qabs (LgammaApprox.q tab (954 + 1)) ≤ 2 ^ 3 / 2 ^ 53) ∧
    (PolyBound.qabs (LgammaApprox.q tab (954 + 2)) ≤ 1 / 2 ^ 102) ∧
    (2 ^ 3 ≤ -(-92233722477573716961 / 2 ^ 63 : ℚ)) ∧
    (-(-46116861715858138147 / 2 ^ 62 : ℚ) < 2 ^ (3 + 1)) ∧
    (-(1 / 2) ≤ LgammaApprox.q tab 954 + (-46116861715858138147 / 2 ^ 62 : ℚ)) ∧
    (LgammaApprox.q tab 954 + (-92233722477573716961 / 2 ^ 63 : ℚ) ≤ 1 / 2) ∧
    (-(994599 / 2 ^ 20 : ℚ) + 1 / 2 ^ 40 ≤ 2 ^ 24 * ((-46116861715858138147 / 2 ^ 62 : ℚ) + LgammaApprox.rootX0 954)) ∧
    (2 ^ 24 * ((-92233722477573716961 / 2 ^ 63 : ℚ) + LgammaApprox.rootX0 954) ≤ (206321 / 2 ^ 18 : ℚ) - 1 / 2 ^ 40) ∧
    ((206321 / 2 ^ 18 : ℚ) ≤ 1 ∧ (994599 / 2 ^ 20 : ℚ) ≤ 1 ∧ 0 ≤ (206321 / 2 ^ 18 : ℚ) ∧ 0 ≤ (994599 / 2 ^ 20 : ℚ)) ∧
    ((206321 / 2 ^ 18 : ℚ) + (243 / 2 ^ 58 : ℚ) ≤ (273393291368595699 / 2 ^ 58 : ℚ) ∧ (994599 / 2 ^ 20 : ℚ) + (243 / 2 ^ 58 : ℚ) ≤ (273393291368595699 / 2 ^ 58 : ℚ)) ∧
    ((206321 / 2 ^ 18 : ℚ) / 2 ^ 50 + 2 ^ 24 / 2 ^ 99 ≤ (243 / 2 ^ 58 : ℚ) ∧ (994599 / 2 ^ 20 : ℚ) / 2 ^ 50 + 2 ^ 24 / 2 ^ 99 ≤ (243 / 2 ^ 58 : ℚ)) ∧
    ((273393291368595699 / 2 ^ 58 : ℚ) ≤ (273393291368595699 / 2 ^ 58 : ℚ) ∧ (273393291368595699 / 2 ^ 58 : ℚ) ≤ (273393291368595699 / 2 ^ 58 : ℚ)) ∧
    ((4171149470241 / 2 ^ 20 : ℚ) ≤ 2 * (1707376985267 / 2 ^ 19 : ℚ)) ∧
    ((141912585019 / 2 ^ 18 : ℚ) ≤ (1707376985267 / 2 ^ 19 : ℚ)) ∧
    ((E16).getD (21 - 1) 0 ≤ (1707376985267 / 2 ^ 19 : ℚ) / 2 ^ 70) ∧
    ((L16).getD (21 - 1) 0 ≤ 1 / 2 ^ 15) ∧
    ((4171149470241 / 2 ^ 20 : ℚ) ≤ 2 ^ 29) ∧
    (1 ≤ (1707376985267 / 2 ^ 19 : ℚ)) ∧
    (0 < (1707376985267 / 2 ^ 19 : ℚ) ∧ ((1707376985267 / 2 ^ 19 : ℚ) ≤ (1707376985267 / 2 ^ 19 : ℚ) ∧ (4171149470241 / 2 ^ 20 : ℚ) ≤ (4171149470241 / 2 ^ 20 : ℚ))) := by
  decide +kernel

end Library.Numerics.Float64.Lgamma.LgammaRootKern
