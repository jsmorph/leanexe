import Verified.Examples.LgammaAsymSeries

/-!
The kernel checks of the three polynomials of `Lgamma.asLgammaAsymAccurate`'s Stirling series,
in `Lgamma.asymTable` at offsets 2, 18, and 42 with 7, 11, and 27 pairs, for `x` from 48, from
14.5 to 48, and from 3.75 to 14.5.  Each satisfies `LgammaPolyIv.stepsIvOk` at the square
`z2h + z2l` of `1/x` (`asym1_ok`, `asym2_ok`, `asym3_ok`), takes values in `[0.0831, 0.0834]`
(`asym1_val`, ...), and has a Lipschitz constant below `2^-8` on its interval (`asym1_lip`, ...).
The third uses eight subintervals of `[0, 1/14]`, since its coefficients alternate in sign and
grow to `2.4 · 10^14`.  The exponents of the bounds come from a script that checks each condition
in exact arithmetic before the kernel does.
-/

namespace Verified.Examples.LgammaAsymKern
open LgammaPolyIv LgammaAsymSeries

set_option exponentiation.threshold 4096

/-- The bounds of the polynomial from 48: `x ≥ 48`, `1/x² ≤ 1/2300`. -/
def a1C : List ℚ := pz [3, 8, 10, 10, 10, 9, 7]
def a1Cl : List ℚ := pz [57, 63, 65, 64, 64, 63, 62]
def a1E : List ℚ := pz [115, 112, 113, 113, 114, 112, 107]
def a1Λ : List ℚ := pz [61, 59, 60, 60, 60, 58, 53]
def a1K : List ℚ := pz [7, 9, 10, 10, 10, 8]

/-- The bounds of the polynomial from 14.5 to 48: `1/x² ≤ 1/210`. -/
def a2C : List ℚ := pz [3, 8, 10, 10, 10, 9, 7, 5, 2, -1, -4]
def a2Cl : List ℚ := pz [57, 63, 64, 65, 64, 63, 62, 59, 56, 53, 50]
def a2E : List ℚ := pz [103, 99, 101, 104, 107, 109, 111, 112, 112, 111, 107]
def a2Λ : List ℚ := pz [49, 48, 51, 54, 57, 59, 60, 60, 60, 58, 53]
def a2K : List ℚ := pz [-4, -1, 2, 5, 7, 9, 10, 10, 10, 8]

/-- The bounds of the polynomial from 3.75 to 14.5: `1/x² ≤ 1/14`. -/
def a3C : List ℚ := pz [3, 8, 10, 10, 10, 9, 7, 5, 2, -1, -4, -8, -11, -15, -19, -23, -27, -30, -33,
  -37, -39, -42, -44, -46, -48, -48, -48]
def a3Cl : List ℚ := pz [57, 62, 64, 65, 65, 64, 63, 60, 56, 55, 51, 47, 44, 39, 35, 31, 28, 24, 22,
  18, 18, 12, 10, 10, 7, 7, 6]
def a3E : List ℚ := pz [59, 51, 50, 50, 50, 52, 54, 56, 58, 60, 62, 65, 68, 71, 74, 77, 80, 83, 86,
  89, 92, 95, 98, 101, 104, 106, 106]
def a3Λ : List ℚ := pz [5, 1, 1, 1, 3, 5, 7, 9, 11, 14, 17, 20, 23, 26, 29, 32, 35, 38, 41, 44, 47,
  50, 53, 56, 58, 58, 53]
def a3K : List ℚ := pz [-48, -48, -48, -46, -44, -42, -39, -37, -33, -30, -27, -23, -19, -15, -11,
  -8, -4, -1, 2, 5, 7, 9, 10, 10, 10, 8]

theorem asym1_ok : stepsIvOk Lgamma.asymTable 2 7 1 (1 / 2300) (1 / 2300) (1 / 2 ^ 58)
    a1C a1Cl a1E a1Λ a1K = true := by decide +kernel

theorem asym2_ok : stepsIvOk Lgamma.asymTable 18 11 1 (1 / 210) (1 / 210) (1 / 2 ^ 54)
    a2C a2Cl a2E a2Λ a2K = true := by decide +kernel

theorem asym3_ok : stepsIvOk Lgamma.asymTable 42 27 8 (1 / 14) (1 / 14) (1 / 2 ^ 50)
    a3C a3Cl a3E a3Λ a3K = true := by decide +kernel

theorem asym1_val : valOk Lgamma.asymTable 2 7 1 (1 / 2300) (831 / 10000) (834 / 10000) = true := by
  decide +kernel

theorem asym2_val : valOk Lgamma.asymTable 18 11 1 (1 / 210) (831 / 10000) (834 / 10000) = true := by
  decide +kernel

theorem asym3_val : valOk Lgamma.asymTable 42 27 8 (1 / 14) (831 / 10000) (834 / 10000) = true := by
  decide +kernel

theorem asym1_lip :
    TgammaPolyLip.lipQ (1 / 2300) (LgammaApprox.ddCoeffs Lgamma.asymTable 2 7) ≤ 1 / 2 ^ 8 := by
  decide +kernel

theorem asym2_lip :
    TgammaPolyLip.lipQ (1 / 210) (LgammaApprox.ddCoeffs Lgamma.asymTable 18 11) ≤ 1 / 2 ^ 8 := by
  decide +kernel

theorem asym3_lip :
    TgammaPolyLip.lipQ (1 / 14) (LgammaApprox.ddCoeffs Lgamma.asymTable 42 27) ≤ 1 / 2 ^ 8 := by
  decide +kernel

/-- The last error and low-part bounds of the three checks. -/
theorem asym_ends :
    a1E.getD (7 - 1) 0 ≤ 1 / 2 ^ 105 ∧ a1Λ.getD (7 - 1) 0 ≤ 1 / 2 ^ 52 ∧
      a2E.getD (11 - 1) 0 ≤ 1 / 2 ^ 105 ∧ a2Λ.getD (11 - 1) 0 ≤ 1 / 2 ^ 52 ∧
      a3E.getD (27 - 1) 0 ≤ 1 / 2 ^ 105 ∧ a3Λ.getD (27 - 1) 0 ≤ 1 / 2 ^ 52 := by
  decide +kernel

#print axioms asym1_ok
#print axioms asym2_ok
#print axioms asym3_ok
#print axioms asym1_val
#print axioms asym2_val
#print axioms asym3_val
#print axioms asym1_lip
#print axioms asym2_lip
#print axioms asym3_lip
#print axioms asym_ends

end Verified.Examples.LgammaAsymKern
