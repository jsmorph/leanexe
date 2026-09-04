import Project.EulerRusanov.RealStencil
import Project.EulerRusanov.InterfaceData
import CodeLib.Numerical.ErrorComposition

/-!
# Decoded numerical error for the two-cell Euler stencil

This module assembles the three frozen `sodLL`, `sodLR`, and `sodRR` flux
words in exact real arithmetic and propagates their already proved
componentwise error budgets through a two-cell finite-volume update.  The
right pressure is the exact dyadic value decoded from binary64 `0.1`; its
difference from mathematical `1 / 10` is proved explicitly.

The update arithmetic in this file is mathematical real arithmetic.  The
three flux words come from the artifact model, but this module does not claim
that the cell updates themselves executed in WebAssembly.
-/

namespace Project.EulerRusanov.StencilNumerical

open Project.EulerRusanov.RealConservative
open Project.EulerRusanov.RealStencil

set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-! ## Generic componentwise propagation -/

/-- Decode the three raw flux words into an exact-real vector. -/
noncomputable def fluxBitsValueVec (flux : Model.FluxBits) : Vec3 :=
  ![CodeLib.IEEE64.value flux.mass,
    CodeLib.IEEE64.value flux.momentum,
    CodeLib.IEEE64.value flux.energy]

/-- The public componentwise error budgets of the scalar flux artifact. -/
noncomputable def fluxErrorBudgetVec : Vec3 :=
  ![Numerical.massErrorBudget,
    Numerical.momentumErrorBudget,
    Numerical.energyErrorBudget]

/-- Pointwise absolute error between two conservative or flux vectors. -/
def ComponentwiseError (approximate exact budget : Vec3) : Prop :=
  ∀ i, |approximate i - exact i| ≤ budget i

/-- Error accumulated by one exact-real update from its two interface fluxes. -/
noncomputable def updateErrorBudget
    (stepRatio : ℝ) (left right : Vec3) : Vec3 :=
  fun i => |stepRatio| * (left i + right i)

/-- Errors of two independently perturbed terms add under subtraction. -/
theorem difference_perturbations
    {x x₀ y y₀ eₓ eᵧ : ℝ}
    (hx : |x - x₀| ≤ eₓ) (hy : |y - y₀| ≤ eᵧ) :
    |(x - y) - (x₀ - y₀)| ≤ eₓ + eᵧ := by
  rw [show (x - y) - (x₀ - y₀) = (x - x₀) + (y₀ - y) by ring]
  exact (abs_add_le _ _).trans
    (add_le_add hx (by simpa [abs_sub_comm] using hy))

/-- Exact signed error identity for a cell update. -/
theorem cellUpdate_sub_eq
    (stepRatio : ℝ) (state : Vec3)
    (approxLeft approxRight exactLeft exactRight : Vec3) (i : Fin 3) :
    cellUpdate stepRatio state approxLeft approxRight i -
        cellUpdate stepRatio state exactLeft exactRight i =
      stepRatio *
        ((approxLeft i - exactLeft i) -
          (approxRight i - exactRight i)) := by
  simp only [cellUpdate]
  ring

/-- Exact-real cell assembly introduces no error beyond the two supplied
interface-flux errors. -/
theorem cellUpdate_componentwise_error
    {stepRatio : ℝ} {state : Vec3}
    {approxLeft approxRight exactLeft exactRight errorLeft errorRight : Vec3}
    (hleft : ComponentwiseError approxLeft exactLeft errorLeft)
    (hright : ComponentwiseError approxRight exactRight errorRight) :
    ComponentwiseError
      (cellUpdate stepRatio state approxLeft approxRight)
      (cellUpdate stepRatio state exactLeft exactRight)
      (updateErrorBudget stepRatio errorLeft errorRight) := by
  intro i
  rw [cellUpdate_sub_eq, abs_mul]
  rw [show
    (approxLeft i - exactLeft i) - (approxRight i - exactRight i) =
      (approxLeft i - approxRight i) - (exactLeft i - exactRight i) by ring]
  exact mul_le_mul_of_nonneg_left
    (difference_perturbations
      (x := approxLeft i) (x₀ := exactLeft i)
      (y := approxRight i) (y₀ := exactRight i)
      (hleft i) (hright i))
    (abs_nonneg stepRatio)

/-- Componentwise error for both cells of a three-interface update. -/
theorem twoCellStep_componentwise_error
    {stepRatio : ℝ} {stateLeft stateRight : Vec3}
    {approxLL approxLR approxRR exactLL exactLR exactRR : Vec3}
    {errorLL errorLR errorRR : Vec3}
    (hLL : ComponentwiseError approxLL exactLL errorLL)
    (hLR : ComponentwiseError approxLR exactLR errorLR)
    (hRR : ComponentwiseError approxRR exactRR errorRR) :
    ComponentwiseError
        (twoCellStep stepRatio stateLeft stateRight
          approxLL approxLR approxRR).1
        (twoCellStep stepRatio stateLeft stateRight
          exactLL exactLR exactRR).1
        (updateErrorBudget stepRatio errorLL errorLR) ∧
      ComponentwiseError
        (twoCellStep stepRatio stateLeft stateRight
          approxLL approxLR approxRR).2
        (twoCellStep stepRatio stateLeft stateRight
          exactLL exactLR exactRR).2
        (updateErrorBudget stepRatio errorLR errorRR) := by
  constructor
  · exact cellUpdate_componentwise_error hLL hLR
  · exact cellUpdate_componentwise_error hLR hRR

/-- The shared interface cancels from the two-cell balance residual.  Thus
only the two boundary-flux error budgets occur in this bound. -/
theorem twoCellStep_balance_residual_le
    {stepRatio : ℝ} {stateLeft stateRight : Vec3}
    {approxLL approxLR approxRR exactLL exactRR : Vec3}
    {errorLL errorRR : Vec3}
    (hLL : ComponentwiseError approxLL exactLL errorLL)
    (hRR : ComponentwiseError approxRR exactRR errorRR) (i : Fin 3) :
    |((twoCellStep stepRatio stateLeft stateRight
          approxLL approxLR approxRR).1 i +
        (twoCellStep stepRatio stateLeft stateRight
          approxLL approxLR approxRR).2 i) -
      (stateLeft i + stateRight i -
        stepRatio * (exactRR i - exactLL i))| ≤
      updateErrorBudget stepRatio errorLL errorRR i := by
  rw [twoCellStep_balance]
  rw [show
      (stateLeft i + stateRight i - stepRatio * (approxRR i - approxLL i)) -
          (stateLeft i + stateRight i - stepRatio * (exactRR i - exactLL i)) =
        -stepRatio *
          ((approxRR i - exactRR i) - (approxLL i - exactLL i)) by ring,
    abs_mul, abs_neg]
  rw [show
    (approxRR i - exactRR i) - (approxLL i - exactLL i) =
      (approxRR i - approxLL i) - (exactRR i - exactLL i) by ring]
  have hdifference := difference_perturbations
      (x := approxRR i) (x₀ := exactRR i)
      (y := approxLL i) (y₀ := exactLL i)
      (hRR i) (hLL i)
  exact mul_le_mul_of_nonneg_left
    (by simpa [add_comm] using hdifference) (abs_nonneg stepRatio)

/-! ## Bridge from the scalar flux theorem -/

/-- Vector form of the existing public scalar-flux real-error contract. -/
theorem fluxRealError_componentwise
    {rhoL uL pL rhoR uR pR : UInt64} {result : Model.FluxBits}
    (herror : Numerical.FluxRealError
      rhoL uL pL rhoR uR pR result) :
    ComponentwiseError
      (fluxBitsValueVec result)
      (rusanovFluxVec
        (Model.primitiveRealOfBits rhoL uL pL)
        (Model.primitiveRealOfBits rhoR uR pR))
      fluxErrorBudgetVec := by
  intro i
  fin_cases i
  · simpa [fluxBitsValueVec, fluxErrorBudgetVec, rusanovFluxVec,
      fluxRealVec, Model.rusanovRealOfBits] using herror.massError
  · simpa [fluxBitsValueVec, fluxErrorBudgetVec, rusanovFluxVec,
      fluxRealVec, Model.rusanovRealOfBits] using herror.momentumError
  · simpa [fluxBitsValueVec, fluxErrorBudgetVec, rusanovFluxVec,
      fluxRealVec, Model.rusanovRealOfBits] using herror.energyError

private theorem row_flux_error
    (row : InterfaceData.Row)
    (hguard : Model.eulerGuard row.rhoL row.uL row.pL
      row.rhoR row.uR row.pR = true)
    (hmodel : InterfaceData.modelResult row = row.expected) :
    Numerical.FluxRealError row.rhoL row.uL row.pL
      row.rhoR row.uR row.pR row.fluxBits := by
  have hnumeric :=
    Numerical.checkedFluxBitsModel_real_error_of_guard hguard
  change
    (Model.checkedFluxBitsModel row.rhoL row.uL row.pL
        row.rhoR row.uR row.pR).status = 0 ∧
      Numerical.FluxRealError row.rhoL row.uL row.pL
        row.rhoR row.uR row.pR
        { mass := (Model.checkedFluxBitsModel row.rhoL row.uL row.pL
            row.rhoR row.uR row.pR).mass
          momentum := (Model.checkedFluxBitsModel row.rhoL row.uL row.pL
            row.rhoR row.uR row.pR).momentum
          energy := (Model.checkedFluxBitsModel row.rhoL row.uL row.pL
            row.rhoR row.uR row.pR).energy } at hnumeric
  change Model.checkedFluxBitsModel row.rhoL row.uL row.pL
      row.rhoR row.uR row.pR = row.expected at hmodel
  rw [hmodel] at hnumeric
  simpa only [InterfaceData.Row.fluxBits] using hnumeric.2

theorem sodLL_flux_error :
    Numerical.FluxRealError InterfaceData.sodLL.rhoL
      InterfaceData.sodLL.uL InterfaceData.sodLL.pL
      InterfaceData.sodLL.rhoR InterfaceData.sodLL.uR
      InterfaceData.sodLL.pR InterfaceData.sodLL.fluxBits :=
  row_flux_error InterfaceData.sodLL InterfaceData.sodLL_guard
    InterfaceData.sodLL_model

theorem sodLR_flux_error :
    Numerical.FluxRealError InterfaceData.sodLR.rhoL
      InterfaceData.sodLR.uL InterfaceData.sodLR.pL
      InterfaceData.sodLR.rhoR InterfaceData.sodLR.uR
      InterfaceData.sodLR.pR InterfaceData.sodLR.fluxBits :=
  row_flux_error InterfaceData.sodLR InterfaceData.sodLR_guard
    InterfaceData.sodLR_model

theorem sodRR_flux_error :
    Numerical.FluxRealError InterfaceData.sodRR.rhoL
      InterfaceData.sodRR.uL InterfaceData.sodRR.pL
      InterfaceData.sodRR.rhoR InterfaceData.sodRR.uR
      InterfaceData.sodRR.pR InterfaceData.sodRR.fluxBits :=
  row_flux_error InterfaceData.sodRR InterfaceData.sodRR_guard
    InterfaceData.sodRR_model

/-! ## Exact decoded Sod inputs -/

/-- Exact positive bias of binary64 `0.1` above mathematical `1 / 10`. -/
noncomputable def tenthRepresentationError : ℝ :=
  1 / 180143985094819840

theorem tenthRepresentationError_eq_epsilon_div_40 :
    tenthRepresentationError =
      CodeLib.Numerical.Kernels.f64Epsilon / 40 := by
  norm_num [tenthRepresentationError,
    CodeLib.Numerical.Kernels.f64Epsilon]

private theorem value_zero :
    CodeLib.IEEE64.value (0x0000000000000000 : UInt64) = 0 := by
  have hbits : (0x0000000000000000 : UInt64) =
      Wasm.IEEE64.encodeFinite false 0 0 := by
    norm_num [Wasm.IEEE64.encodeFinite]
    rfl
  rw [hbits, CodeLib.IEEE64.value,
    CodeLib.IEEE64.scaledValue_encodeFinite false 0 0
      (by norm_num) (by norm_num)]
  norm_num

private theorem value_one :
    CodeLib.IEEE64.value (0x3FF0000000000000 : UInt64) = 1 := by
  have hbits : (0x3FF0000000000000 : UInt64) =
      Wasm.IEEE64.encodeFinite false 1023 0 := by
    norm_num [Wasm.IEEE64.encodeFinite]
    rfl
  rw [hbits, CodeLib.IEEE64.value,
    CodeLib.IEEE64.scaledValue_encodeFinite false 1023 0
      (by norm_num) (by norm_num)]
  norm_num [pow_succ]

private theorem value_one_eighth :
    CodeLib.IEEE64.value (0x3FC0000000000000 : UInt64) = (1 : ℝ) / 8 := by
  have hbits : (0x3FC0000000000000 : UInt64) =
      Wasm.IEEE64.encodeFinite false 1020 0 := by
    norm_num [Wasm.IEEE64.encodeFinite]
    rfl
  rw [hbits, CodeLib.IEEE64.value,
    CodeLib.IEEE64.scaledValue_encodeFinite false 1020 0
      (by norm_num) (by norm_num)]
  norm_num [pow_succ]

/-- Exact-real value of the frozen binary64 word for decimal `0.1`. -/
theorem value_sod_pressure :
    CodeLib.IEEE64.value (0x3FB999999999999A : UInt64) =
      (1 : ℝ) / 10 + tenthRepresentationError := by
  have hbits : (0x3FB999999999999A : UInt64) =
      Wasm.IEEE64.encodeFinite false 1019 2702159776422298 := by
    norm_num [Wasm.IEEE64.encodeFinite]
    rfl
  rw [hbits, CodeLib.IEEE64.value,
    CodeLib.IEEE64.scaledValue_encodeFinite false 1019 2702159776422298
      (by norm_num) (by norm_num)]
  norm_num [tenthRepresentationError, pow_succ]

/-- Left primitive state decoded from the frozen `sodLR` input row. -/
noncomputable def decodedSodLeft : Model.PrimitiveReal :=
  Model.primitiveRealOfBits InterfaceData.sodLR.rhoL
    InterfaceData.sodLR.uL InterfaceData.sodLR.pL

/-- Right primitive state decoded from the frozen `sodLR` input row. -/
noncomputable def decodedSodRight : Model.PrimitiveReal :=
  Model.primitiveRealOfBits InterfaceData.sodLR.rhoR
    InterfaceData.sodLR.uR InterfaceData.sodLR.pR

theorem decodedSodLeft_eq : decodedSodLeft = sodLeft := by
  simp [decodedSodLeft, sodLeft, Model.primitiveRealOfBits,
    InterfaceData.sodLR, value_zero, value_one]

theorem decodedSodRight_eq :
    decodedSodRight =
      { rho := (1 : ℝ) / 8
        velocity := 0
        pressure := (1 : ℝ) / 10 + tenthRepresentationError } := by
  simp [decodedSodRight, Model.primitiveRealOfBits, InterfaceData.sodLR,
    value_zero, value_one_eighth, value_sod_pressure]

/-! ## Frozen-flux assembly and decoded exact reference -/

/-- Exact-real Rusanov stencil at the primitive values decoded from the input
words. -/
noncomputable def decodedExactTransmissiveStep
    (stepRatio : ℝ) : Vec3 × Vec3 :=
  transmissiveTwoCellStep stepRatio decodedSodLeft decodedSodRight

/-- Exact-real assembly of the three frozen artifact flux words.  Despite the
decoded inputs and outputs, this definition does not execute update arithmetic
in WebAssembly. -/
noncomputable def decodedTransmissiveStep
    (stepRatio : ℝ) : Vec3 × Vec3 :=
  twoCellStep stepRatio
    (primitiveToConservative decodedSodLeft)
    (primitiveToConservative decodedSodRight)
    (fluxBitsValueVec InterfaceData.sodLL.fluxBits)
    (fluxBitsValueVec InterfaceData.sodLR.fluxBits)
    (fluxBitsValueVec InterfaceData.sodRR.fluxBits)

private theorem sodLL_componentwise :
    ComponentwiseError
      (fluxBitsValueVec InterfaceData.sodLL.fluxBits)
      (rusanovFluxVec decodedSodLeft decodedSodLeft)
      fluxErrorBudgetVec := by
  have h := fluxRealError_componentwise sodLL_flux_error
  simpa [decodedSodLeft, InterfaceData.sodLL, InterfaceData.sodLR] using h

private theorem sodLR_componentwise :
    ComponentwiseError
      (fluxBitsValueVec InterfaceData.sodLR.fluxBits)
      (rusanovFluxVec decodedSodLeft decodedSodRight)
      fluxErrorBudgetVec := by
  exact fluxRealError_componentwise sodLR_flux_error

private theorem sodRR_componentwise :
    ComponentwiseError
      (fluxBitsValueVec InterfaceData.sodRR.fluxBits)
      (rusanovFluxVec decodedSodRight decodedSodRight)
      fluxErrorBudgetVec := by
  have h := fluxRealError_componentwise sodRR_flux_error
  simpa [decodedSodRight, InterfaceData.sodRR, InterfaceData.sodLR] using h

/-- Both assembled cells are bounded against the decoded-input exact-real
stencil.  At a general step ratio, each cell pays for exactly two interface
flux budgets. -/
theorem decodedTransmissiveStep_error (stepRatio : ℝ) :
    ComponentwiseError
        (decodedTransmissiveStep stepRatio).1
        (decodedExactTransmissiveStep stepRatio).1
        (updateErrorBudget stepRatio fluxErrorBudgetVec fluxErrorBudgetVec) ∧
      ComponentwiseError
        (decodedTransmissiveStep stepRatio).2
        (decodedExactTransmissiveStep stepRatio).2
        (updateErrorBudget stepRatio fluxErrorBudgetVec fluxErrorBudgetVec) := by
  simpa [decodedTransmissiveStep, decodedExactTransmissiveStep,
    transmissiveTwoCellStep] using
    (twoCellStep_componentwise_error sodLL_componentwise
      sodLR_componentwise sodRR_componentwise)

/-- The balance residual against the exact decoded-input boundary fluxes does
not include the shared `sodLR` flux error. -/
theorem decodedTransmissiveStep_balance_residual_le
    (stepRatio : ℝ) (i : Fin 3) :
    |((decodedTransmissiveStep stepRatio).1 i +
        (decodedTransmissiveStep stepRatio).2 i) -
      (primitiveToConservative decodedSodLeft i +
        primitiveToConservative decodedSodRight i -
        stepRatio *
          (rusanovFluxVec decodedSodRight decodedSodRight i -
            rusanovFluxVec decodedSodLeft decodedSodLeft i))| ≤
      updateErrorBudget stepRatio fluxErrorBudgetVec fluxErrorBudgetVec i := by
  simpa [decodedTransmissiveStep] using
    (twoCellStep_balance_residual_le
      (stepRatio := stepRatio)
      (stateLeft := primitiveToConservative decodedSodLeft)
      (stateRight := primitiveToConservative decodedSodRight)
      (approxLL := fluxBitsValueVec InterfaceData.sodLL.fluxBits)
      (approxLR := fluxBitsValueVec InterfaceData.sodLR.fluxBits)
      (approxRR := fluxBitsValueVec InterfaceData.sodRR.fluxBits)
      (exactLL := rusanovFluxVec decodedSodLeft decodedSodLeft)
      (exactRR := rusanovFluxVec decodedSodRight decodedSodRight)
      sodLL_componentwise sodRR_componentwise i)

/-- Quarter-step form of the common per-cell and balance budget. -/
noncomputable def sodQuarterErrorBudget : Vec3 :=
  fun i => fluxErrorBudgetVec i / 2

theorem decodedQuarterStep_error :
    ComponentwiseError
        (decodedTransmissiveStep (1 / 4)).1
        (decodedExactTransmissiveStep (1 / 4)).1
        sodQuarterErrorBudget ∧
      ComponentwiseError
        (decodedTransmissiveStep (1 / 4)).2
        (decodedExactTransmissiveStep (1 / 4)).2
        sodQuarterErrorBudget := by
  have hbudget :
      updateErrorBudget (1 / 4) fluxErrorBudgetVec fluxErrorBudgetVec =
        sodQuarterErrorBudget := by
    funext i
    simp [updateErrorBudget, sodQuarterErrorBudget]
    ring
  rw [← hbudget]
  exact decodedTransmissiveStep_error (1 / 4)

/-- The exact decoded-input quarter-step, exposing only the input
representation bias relative to the rational reference in `RealStencil`. -/
theorem decodedExactQuarterStep_exact :
    decodedExactTransmissiveStep (1 / 4) =
      (![(207 : ℝ) / 256,
          9 / 80 - tenthRepresentationError / 8,
          257 / 128 + 35 * tenthRepresentationError / 64],
        ![(81 : ℝ) / 256,
          9 / 80 - tenthRepresentationError / 8,
          95 / 128 + 125 * tenthRepresentationError / 64]) := by
  rw [decodedExactTransmissiveStep, decodedSodLeft_eq, decodedSodRight_eq]
  apply Prod.ext
  · funext i
    fin_cases i <;>
      norm_num [transmissiveTwoCellStep, twoCellStep, cellUpdate,
        rusanovFluxVec, fluxRealVec, Model.rusanovReal,
        Model.conservativeReal, Model.eulerFluxReal,
        primitiveToConservative, sodLeft, tenthRepresentationError]
  · funext i
    fin_cases i <;>
      norm_num [transmissiveTwoCellStep, twoCellStep, cellUpdate,
        rusanovFluxVec, fluxRealVec, Model.rusanovReal,
        Model.conservativeReal, Model.eulerFluxReal,
        primitiveToConservative, sodLeft, tenthRepresentationError]

#print axioms twoCellStep_componentwise_error
#print axioms twoCellStep_balance_residual_le
#print axioms value_sod_pressure
#print axioms decodedTransmissiveStep_error
#print axioms decodedTransmissiveStep_balance_residual_le
#print axioms decodedExactQuarterStep_exact

end Project.EulerRusanov.StencilNumerical
