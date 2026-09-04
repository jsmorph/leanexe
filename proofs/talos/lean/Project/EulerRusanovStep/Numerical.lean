import Project.EulerRusanovStep.Model
import Project.EulerRusanov.StencilNumerical

/-!
# Decoded numerical certificate for the fixed Euler--Rusanov step

The execution model returns six fixed binary64 payload words.  This module
decodes those exact words without using Lean's native `Float` evaluator and
compares them with the exact-real quarter step at the decoded Sod inputs.

The signed errors expose the rounding actually present in the complete
generated fixed-step computation, including its nested flux and final update
operations.  In particular, the two-cell momentum and energy balances have
small nonzero decoded-real residuals; they are not reported as exact-real
conservation merely because the raw floating-point computation completed.
-/

namespace Project.EulerRusanovStep.Numerical

open Project.EulerRusanov.RealConservative
open Project.EulerRusanov.RealStencil
open Project.EulerRusanov.StencilNumerical

set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-- The two conservative cells obtained by decoding the six result words. -/
noncomputable def decodedCells
    (result : Model.CheckedSodQuarterStepBits) : Vec3 × Vec3 :=
  (![CodeLib.IEEE64.value result.leftDensity,
      CodeLib.IEEE64.value result.leftMomentum,
      CodeLib.IEEE64.value result.leftEnergy],
    ![CodeLib.IEEE64.value result.rightDensity,
      CodeLib.IEEE64.value result.rightMomentum,
      CodeLib.IEEE64.value result.rightEnergy])

/-- Signed rounding error of the emitted left cell against the exact-real
quarter step at the decoded inputs. -/
noncomputable def leftRoundingError : Vec3 :=
  ![0,
    -(3 * CodeLib.Numerical.Kernels.f64Epsilon / 64),
    -(7 * CodeLib.Numerical.Kernels.f64Epsilon / 512)]

/-- Signed rounding error of the emitted right cell against the exact-real
quarter step at the decoded inputs. -/
noncomputable def rightRoundingError : Vec3 :=
  ![0,
    5 * CodeLib.Numerical.Kernels.f64Epsilon / 64,
    -(25 * CodeLib.Numerical.Kernels.f64Epsilon / 512)]

/-- Signed two-cell balance residual contributed by the six rounded update
results. -/
noncomputable def balanceRoundingError : Vec3 :=
  ![0,
    CodeLib.Numerical.Kernels.f64Epsilon / 32,
    -(CodeLib.Numerical.Kernels.f64Epsilon / 16)]

/-- Decoded-real facts carried by the fixed step result.  The componentwise
identities are signed, not merely absolute bounds. -/
structure RealCertificate (result : Model.CheckedSodQuarterStepBits) : Prop where
  statusZero : result.status = 0
  leftDensityFinite : CodeLib.IEEE64.Finite result.leftDensity
  leftMomentumFinite : CodeLib.IEEE64.Finite result.leftMomentum
  leftEnergyFinite : CodeLib.IEEE64.Finite result.leftEnergy
  rightDensityFinite : CodeLib.IEEE64.Finite result.rightDensity
  rightMomentumFinite : CodeLib.IEEE64.Finite result.rightMomentum
  rightEnergyFinite : CodeLib.IEEE64.Finite result.rightEnergy
  decodedExact : decodedCells result =
    (![(207 : ℝ) / 256,
        9 / 80 - CodeLib.Numerical.Kernels.f64Epsilon / 20,
        257 / 128],
      ![(81 : ℝ) / 256,
        9 / 80 + 3 * CodeLib.Numerical.Kernels.f64Epsilon / 40,
        95 / 128])
  leftError : ∀ i,
    (decodedCells result).1 i -
        (decodedExactTransmissiveStep (1 / 4)).1 i =
      leftRoundingError i
  rightError : ∀ i,
    (decodedCells result).2 i -
        (decodedExactTransmissiveStep (1 / 4)).2 i =
      rightRoundingError i
  balanceError : ∀ i,
    ((decodedCells result).1 i + (decodedCells result).2 i) -
        (primitiveToConservative decodedSodLeft i +
          primitiveToConservative decodedSodRight i -
          (1 / 4) *
            (rusanovFluxVec decodedSodRight decodedSodRight i -
              rusanovFluxVec decodedSodLeft decodedSodLeft i)) =
      balanceRoundingError i
  admissible :
    Admissible (decodedCells result).1 ∧
      Admissible (decodedCells result).2

private theorem expected_leftDensity :
    CodeLib.IEEE64.Finite
        Model.expectedSodQuarterStepBits.leftDensity ∧
      CodeLib.IEEE64.value
          Model.expectedSodQuarterStepBits.leftDensity = (207 : ℝ) / 256 := by
  have hbits : Model.expectedSodQuarterStepBits.leftDensity =
      Wasm.IEEE64.encodeFinite false 1022 2779565395017728 := by
    norm_num [Model.expectedSodQuarterStepBits,
      Wasm.IEEE64.encodeFinite]
    rfl
  rw [hbits]
  constructor
  · exact CodeLib.IEEE64.finite_encodeFinite false 1022 2779565395017728
      (by norm_num) (by norm_num)
  · rw [CodeLib.IEEE64.value,
      CodeLib.IEEE64.scaledValue_encodeFinite false 1022 2779565395017728
        (by norm_num) (by norm_num)]
    norm_num [pow_succ]

private theorem expected_leftMomentum :
    CodeLib.IEEE64.Finite
        Model.expectedSodQuarterStepBits.leftMomentum ∧
      CodeLib.IEEE64.value
          Model.expectedSodQuarterStepBits.leftMomentum =
        (9 : ℝ) / 80 - CodeLib.Numerical.Kernels.f64Epsilon / 20 := by
  have hbits : Model.expectedSodQuarterStepBits.leftMomentum =
      Wasm.IEEE64.encodeFinite false 1019 3602879701896396 := by
    norm_num [Model.expectedSodQuarterStepBits,
      Wasm.IEEE64.encodeFinite]
    rfl
  rw [hbits]
  constructor
  · exact CodeLib.IEEE64.finite_encodeFinite false 1019 3602879701896396
      (by norm_num) (by norm_num)
  · rw [CodeLib.IEEE64.value,
      CodeLib.IEEE64.scaledValue_encodeFinite false 1019 3602879701896396
        (by norm_num) (by norm_num)]
    norm_num [CodeLib.Numerical.Kernels.f64Epsilon, pow_succ]

private theorem expected_leftEnergy :
    CodeLib.IEEE64.Finite
        Model.expectedSodQuarterStepBits.leftEnergy ∧
      CodeLib.IEEE64.value
          Model.expectedSodQuarterStepBits.leftEnergy = (257 : ℝ) / 128 := by
  have hbits : Model.expectedSodQuarterStepBits.leftEnergy =
      Wasm.IEEE64.encodeFinite false 1024 17592186044416 := by
    norm_num [Model.expectedSodQuarterStepBits,
      Wasm.IEEE64.encodeFinite]
    rfl
  rw [hbits]
  constructor
  · exact CodeLib.IEEE64.finite_encodeFinite false 1024 17592186044416
      (by norm_num) (by norm_num)
  · rw [CodeLib.IEEE64.value,
      CodeLib.IEEE64.scaledValue_encodeFinite false 1024 17592186044416
        (by norm_num) (by norm_num)]
    norm_num [pow_succ]

private theorem expected_rightDensity :
    CodeLib.IEEE64.Finite
        Model.expectedSodQuarterStepBits.rightDensity ∧
      CodeLib.IEEE64.value
          Model.expectedSodQuarterStepBits.rightDensity = (81 : ℝ) / 256 := by
  have hbits : Model.expectedSodQuarterStepBits.rightDensity =
      Wasm.IEEE64.encodeFinite false 1021 1196268651020288 := by
    norm_num [Model.expectedSodQuarterStepBits,
      Wasm.IEEE64.encodeFinite]
    rfl
  rw [hbits]
  constructor
  · exact CodeLib.IEEE64.finite_encodeFinite false 1021 1196268651020288
      (by norm_num) (by norm_num)
  · rw [CodeLib.IEEE64.value,
      CodeLib.IEEE64.scaledValue_encodeFinite false 1021 1196268651020288
        (by norm_num) (by norm_num)]
    norm_num [pow_succ]

private theorem expected_rightMomentum :
    CodeLib.IEEE64.Finite
        Model.expectedSodQuarterStepBits.rightMomentum ∧
      CodeLib.IEEE64.value
          Model.expectedSodQuarterStepBits.rightMomentum =
        (9 : ℝ) / 80 +
          3 * CodeLib.Numerical.Kernels.f64Epsilon / 40 := by
  have hbits : Model.expectedSodQuarterStepBits.rightMomentum =
      Wasm.IEEE64.encodeFinite false 1019 3602879701896398 := by
    norm_num [Model.expectedSodQuarterStepBits,
      Wasm.IEEE64.encodeFinite]
    rfl
  rw [hbits]
  constructor
  · exact CodeLib.IEEE64.finite_encodeFinite false 1019 3602879701896398
      (by norm_num) (by norm_num)
  · rw [CodeLib.IEEE64.value,
      CodeLib.IEEE64.scaledValue_encodeFinite false 1019 3602879701896398
        (by norm_num) (by norm_num)]
    norm_num [CodeLib.Numerical.Kernels.f64Epsilon, pow_succ]

private theorem expected_rightEnergy :
    CodeLib.IEEE64.Finite
        Model.expectedSodQuarterStepBits.rightEnergy ∧
      CodeLib.IEEE64.value
          Model.expectedSodQuarterStepBits.rightEnergy = (95 : ℝ) / 128 := by
  have hbits : Model.expectedSodQuarterStepBits.rightEnergy =
      Wasm.IEEE64.encodeFinite false 1022 2181431069507584 := by
    norm_num [Model.expectedSodQuarterStepBits,
      Wasm.IEEE64.encodeFinite]
    rfl
  rw [hbits]
  constructor
  · exact CodeLib.IEEE64.finite_encodeFinite false 1022 2181431069507584
      (by norm_num) (by norm_num)
  · rw [CodeLib.IEEE64.value,
      CodeLib.IEEE64.scaledValue_encodeFinite false 1022 2181431069507584
        (by norm_num) (by norm_num)]
    norm_num [pow_succ]

/-- Exact real values decoded from the six frozen expected words. -/
theorem expected_decodedCells_exact :
    decodedCells Model.expectedSodQuarterStepBits =
      (![(207 : ℝ) / 256,
          9 / 80 - CodeLib.Numerical.Kernels.f64Epsilon / 20,
          257 / 128],
        ![(81 : ℝ) / 256,
          9 / 80 + 3 * CodeLib.Numerical.Kernels.f64Epsilon / 40,
          95 / 128]) := by
  apply Prod.ext
  · funext i
    fin_cases i
    · exact expected_leftDensity.2
    · exact expected_leftMomentum.2
    · exact expected_leftEnergy.2
  · funext i
    fin_cases i
    · exact expected_rightDensity.2
    · exact expected_rightMomentum.2
    · exact expected_rightEnergy.2

/-- Exact real values decoded from the independent pure model result. -/
theorem sodQuarterStepCheckedBitsModel_decodedCells_exact :
    decodedCells Model.sodQuarterStepCheckedBitsModel =
      (![(207 : ℝ) / 256,
          9 / 80 - CodeLib.Numerical.Kernels.f64Epsilon / 20,
          257 / 128],
        ![(81 : ℝ) / 256,
          9 / 80 + 3 * CodeLib.Numerical.Kernels.f64Epsilon / 40,
          95 / 128]) := by
  rw [Model.sodQuarterStepCheckedBitsModel_exact]
  exact expected_decodedCells_exact

/-- Exact signed per-cell error against the decoded-input real quarter step. -/
theorem expected_cell_errors :
    (∀ i,
      (decodedCells Model.expectedSodQuarterStepBits).1 i -
          (decodedExactTransmissiveStep (1 / 4)).1 i =
        leftRoundingError i) ∧
    (∀ i,
      (decodedCells Model.expectedSodQuarterStepBits).2 i -
          (decodedExactTransmissiveStep (1 / 4)).2 i =
        rightRoundingError i) := by
  rw [expected_decodedCells_exact, decodedExactQuarterStep_exact]
  constructor <;> intro i <;> fin_cases i <;>
    norm_num [leftRoundingError, rightRoundingError,
      tenthRepresentationError,
      CodeLib.Numerical.Kernels.f64Epsilon]

/-- Exact signed two-cell balance residual of the rounded result words. -/
theorem expected_balance_error : ∀ i,
    ((decodedCells Model.expectedSodQuarterStepBits).1 i +
        (decodedCells Model.expectedSodQuarterStepBits).2 i) -
      (primitiveToConservative decodedSodLeft i +
        primitiveToConservative decodedSodRight i -
        (1 / 4) *
          (rusanovFluxVec decodedSodRight decodedSodRight i -
            rusanovFluxVec decodedSodLeft decodedSodLeft i)) =
    balanceRoundingError i := by
  intro i
  have hbalance :
      (decodedExactTransmissiveStep (1 / 4)).1 i +
          (decodedExactTransmissiveStep (1 / 4)).2 i =
        primitiveToConservative decodedSodLeft i +
          primitiveToConservative decodedSodRight i -
          (1 / 4) *
            (rusanovFluxVec decodedSodRight decodedSodRight i -
              rusanovFluxVec decodedSodLeft decodedSodLeft i) := by
    simpa only [decodedExactTransmissiveStep] using
      (transmissiveTwoCellStep_balance
        (1 / 4) decodedSodLeft decodedSodRight i)
  rw [← hbalance]
  calc
    ((decodedCells Model.expectedSodQuarterStepBits).1 i +
          (decodedCells Model.expectedSodQuarterStepBits).2 i) -
        ((decodedExactTransmissiveStep (1 / 4)).1 i +
          (decodedExactTransmissiveStep (1 / 4)).2 i) =
      ((decodedCells Model.expectedSodQuarterStepBits).1 i -
          (decodedExactTransmissiveStep (1 / 4)).1 i) +
        ((decodedCells Model.expectedSodQuarterStepBits).2 i -
          (decodedExactTransmissiveStep (1 / 4)).2 i) := by ring
    _ = leftRoundingError i + rightRoundingError i := by
      rw [expected_cell_errors.1 i, expected_cell_errors.2 i]
    _ = balanceRoundingError i := by
      fin_cases i <;>
        norm_num [leftRoundingError, rightRoundingError,
          balanceRoundingError] <;>
        ring

/-- Both cells decoded from the actual six result words remain in the open
Euler admissible set. -/
theorem expected_admissible :
    Admissible (decodedCells Model.expectedSodQuarterStepBits).1 ∧
      Admissible (decodedCells Model.expectedSodQuarterStepBits).2 := by
  rw [expected_decodedCells_exact]
  constructor
  · constructor
    · norm_num [density]
    · change 0 < (2 / 5 : ℝ) *
        (257 / 128 -
          (9 / 80 - CodeLib.Numerical.Kernels.f64Epsilon / 20) ^ 2 /
            (2 * (207 / 256)))
      norm_num [CodeLib.Numerical.Kernels.f64Epsilon]
  · constructor
    · norm_num [density]
    · change 0 < (2 / 5 : ℝ) *
        (95 / 128 -
          (9 / 80 + 3 * CodeLib.Numerical.Kernels.f64Epsilon / 40) ^ 2 /
            (2 * (81 / 256)))
      norm_num [CodeLib.Numerical.Kernels.f64Epsilon]

/-- The frozen expected tuple carries all decoded-real numerical facts. -/
theorem expected_realCertificate :
    RealCertificate Model.expectedSodQuarterStepBits := by
  exact
    { statusZero := rfl
      leftDensityFinite := expected_leftDensity.1
      leftMomentumFinite := expected_leftMomentum.1
      leftEnergyFinite := expected_leftEnergy.1
      rightDensityFinite := expected_rightDensity.1
      rightMomentumFinite := expected_rightMomentum.1
      rightEnergyFinite := expected_rightEnergy.1
      decodedExact := expected_decodedCells_exact
      leftError := expected_cell_errors.1
      rightError := expected_cell_errors.2
      balanceError := expected_balance_error
      admissible := expected_admissible }

/-- The independent pure binary64 model has the exact decoded-real
certificate for its emitted result words. -/
theorem sodQuarterStepCheckedBitsModel_real :
    RealCertificate Model.sodQuarterStepCheckedBitsModel := by
  rw [Model.sodQuarterStepCheckedBitsModel_exact]
  exact expected_realCertificate

#print axioms expected_decodedCells_exact
#print axioms sodQuarterStepCheckedBitsModel_decodedCells_exact
#print axioms expected_cell_errors
#print axioms expected_balance_error
#print axioms expected_admissible
#print axioms sodQuarterStepCheckedBitsModel_real

end Project.EulerRusanovStep.Numerical
