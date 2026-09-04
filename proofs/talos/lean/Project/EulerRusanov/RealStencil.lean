import Project.EulerRusanov.RealConservative

/-!
# Exact-real two-cell finite-volume stencil

This module defines an algebraic finite-volume update in conservative
coordinates.  It then instantiates the three interface fluxes of a two-cell
transmissive stencil with `Model.rusanovReal`.  All arithmetic in this file is
over the mathematical reals: no floating-point evaluation, WebAssembly
execution, or claim about compiled update arithmetic is involved.

For a ratio `lambda = Delta t / Delta x`, the two cells use the interfaces
`F_LL`, `F_LR`, and `F_RR`.  The shared interior flux cancels exactly, leaving
only the boundary-flux contribution to the total conservative state.
-/

namespace Project.EulerRusanov.RealStencil

open Project.EulerRusanov.RealConservative

/-! ## Generic conservative update -/

/-- One forward-Euler finite-volume cell update in conservative coordinates.

`fluxLeft` and `fluxRight` are numerical flux vectors at the cell's two
interfaces, and `stepRatio` is `Delta t / Delta x`.
-/
noncomputable def cellUpdate
    (stepRatio : ℝ) (state fluxLeft fluxRight : Vec3) : Vec3 :=
  fun i => state i - stepRatio * (fluxRight i - fluxLeft i)

/-- A two-cell update with the three interface fluxes in spatial order:
left boundary, shared interior interface, and right boundary. -/
noncomputable def twoCellStep
    (stepRatio : ℝ) (stateLeft stateRight : Vec3)
    (fluxLL fluxLR fluxRR : Vec3) : Vec3 × Vec3 :=
  (cellUpdate stepRatio stateLeft fluxLL fluxLR,
    cellUpdate stepRatio stateRight fluxLR fluxRR)

/-- Exact componentwise conservation: the shared interface flux cancels, so
the two-cell total changes only by the net boundary flux. -/
theorem twoCellStep_balance
    (stepRatio : ℝ) (stateLeft stateRight : Vec3)
    (fluxLL fluxLR fluxRR : Vec3) (i : Fin 3) :
    (twoCellStep stepRatio stateLeft stateRight fluxLL fluxLR fluxRR).1 i +
        (twoCellStep stepRatio stateLeft stateRight fluxLL fluxLR fluxRR).2 i =
      stateLeft i + stateRight i -
        stepRatio * (fluxRR i - fluxLL i) := by
  simp only [twoCellStep, cellUpdate]
  ring

/-! ## Exact-real Rusanov transmissive stencil -/

/-- Vector-coordinate view of the independent exact-real Rusanov flux. -/
noncomputable def rusanovFluxVec
    (left right : Model.PrimitiveReal) : Vec3 :=
  fluxRealVec (Model.rusanovReal left right)

/-- Consistency of the exact-real numerical flux: equal states give the
physical Euler flux exactly. -/
theorem rusanovFluxVec_self (state : Model.PrimitiveReal) :
    rusanovFluxVec state state =
      fluxRealVec (Model.eulerFluxReal state) := by
  funext i
  fin_cases i <;>
    simp [rusanovFluxVec, fluxRealVec, Model.rusanovReal] <;>
    ring

/-- One exact-real forward-Euler step for two primitive cells with
transmissive boundary states.  The interfaces are `(left,left)`,
`(left,right)`, and `(right,right)`. -/
noncomputable def transmissiveTwoCellStep
    (stepRatio : ℝ)
    (left right : Model.PrimitiveReal) : Vec3 × Vec3 :=
  twoCellStep stepRatio
    (primitiveToConservative left) (primitiveToConservative right)
    (rusanovFluxVec left left)
    (rusanovFluxVec left right)
    (rusanovFluxVec right right)

/-- Exact balance for the transmissive Rusanov stencil.  In particular, the
interior `(left,right)` flux does not occur in the right-hand side. -/
theorem transmissiveTwoCellStep_balance
    (stepRatio : ℝ)
    (left right : Model.PrimitiveReal) (i : Fin 3) :
    (transmissiveTwoCellStep stepRatio left right).1 i +
        (transmissiveTwoCellStep stepRatio left right).2 i =
      primitiveToConservative left i + primitiveToConservative right i -
        stepRatio *
          (rusanovFluxVec right right i - rusanovFluxVec left left i) := by
  simpa only [transmissiveTwoCellStep] using
    twoCellStep_balance stepRatio
      (primitiveToConservative left) (primitiveToConservative right)
      (rusanovFluxVec left left) (rusanovFluxVec left right)
      (rusanovFluxVec right right) i

/-! ## Canonical Sod data -/

/-- Canonical exact-real left state for the Sod shock tube. -/
def sodLeft : Model.PrimitiveReal :=
  { rho := 1, velocity := 0, pressure := 1 }

/-- Canonical rational exact-real right state for the Sod shock tube.

This uses mathematical `1/10`.  A future artifact-facing stencil must instead
use the exact dyadic value decoded from the binary64 encoding of `0.1` and
prove the bridge explicitly. -/
noncomputable def sodRight : Model.PrimitiveReal :=
  { rho := 1 / 8, velocity := 0, pressure := 1 / 10 }

@[simp] theorem sodLeft_conservative :
    primitiveToConservative sodLeft =
      ![(1 : ℝ), 0, 5 / 2] := by
  funext i
  fin_cases i <;>
    norm_num [primitiveToConservative, sodLeft]

@[simp] theorem sodRight_conservative :
    primitiveToConservative sodRight =
      ![(1 : ℝ) / 8, 0, 1 / 4] := by
  funext i
  fin_cases i <;>
    norm_num [primitiveToConservative, sodRight]

@[simp] theorem sodLL_flux :
    rusanovFluxVec sodLeft sodLeft =
      ![(0 : ℝ), 1, 0] := by
  funext i
  fin_cases i <;>
    norm_num [rusanovFluxVec, fluxRealVec, Model.rusanovReal,
      Model.conservativeReal, Model.eulerFluxReal, sodLeft]

@[simp] theorem sodLR_flux :
    rusanovFluxVec sodLeft sodRight =
      ![(49 : ℝ) / 64, 11 / 20, 63 / 32] := by
  funext i
  fin_cases i <;>
    norm_num [rusanovFluxVec, fluxRealVec, Model.rusanovReal,
      Model.conservativeReal, Model.eulerFluxReal, sodLeft, sodRight]

@[simp] theorem sodRR_flux :
    rusanovFluxVec sodRight sodRight =
      ![(0 : ℝ), 1 / 10, 0] := by
  funext i
  fin_cases i <;>
    norm_num [rusanovFluxVec, fluxRealVec, Model.rusanovReal,
      Model.conservativeReal, Model.eulerFluxReal, sodRight]

/-- A concrete exact-real stencil instance with `Delta t / Delta x = 1/4`.
This name deliberately makes no WebAssembly claim. -/
noncomputable def sodQuarterStep : Vec3 × Vec3 :=
  transmissiveTwoCellStep (1 / 4) sodLeft sodRight

/-- Every conservative coordinate of the canonical quarter-step, exactly. -/
theorem sodQuarterStep_exact :
    sodQuarterStep =
      (![(207 : ℝ) / 256, 9 / 80, 257 / 128],
        ![(81 : ℝ) / 256, 9 / 80, 95 / 128]) := by
  apply Prod.ext
  · funext i
    fin_cases i <;>
      norm_num [sodQuarterStep, transmissiveTwoCellStep, twoCellStep,
        cellUpdate, rusanovFluxVec, fluxRealVec, Model.rusanovReal,
        Model.conservativeReal, Model.eulerFluxReal,
        primitiveToConservative, sodLeft, sodRight]
  · funext i
    fin_cases i <;>
      norm_num [sodQuarterStep, transmissiveTwoCellStep, twoCellStep,
        cellUpdate, rusanovFluxVec, fluxRealVec, Model.rusanovReal,
        Model.conservativeReal, Model.eulerFluxReal,
        primitiveToConservative, sodLeft, sodRight]

/-- The updated left Sod cell remains in the open Euler admissible set. -/
theorem sodQuarterStep_left_admissible :
    Admissible sodQuarterStep.1 := by
  rw [sodQuarterStep_exact]
  constructor
  · norm_num [density]
  · change 0 < ((2 : ℝ) / 5) *
      ((257 : ℝ) / 128 - ((9 : ℝ) / 80) ^ 2 /
        (2 * ((207 : ℝ) / 256)))
    norm_num

/-- The updated right Sod cell remains in the open Euler admissible set. -/
theorem sodQuarterStep_right_admissible :
    Admissible sodQuarterStep.2 := by
  rw [sodQuarterStep_exact]
  constructor
  · norm_num [density]
  · change 0 < ((2 : ℝ) / 5) *
      ((95 : ℝ) / 128 - ((9 : ℝ) / 80) ^ 2 /
        (2 * ((81 : ℝ) / 256)))
    norm_num

/-- The zero mass boundary fluxes make total density exactly conservative. -/
theorem sodQuarterStep_total_density :
    density sodQuarterStep.1 + density sodQuarterStep.2 = 9 / 8 := by
  rw [sodQuarterStep_exact]
  norm_num [density]

/-- Unequal boundary pressures impart the exact net momentum `9/40`. -/
theorem sodQuarterStep_total_momentum :
    momentum sodQuarterStep.1 + momentum sodQuarterStep.2 = 9 / 40 := by
  rw [sodQuarterStep_exact]
  norm_num [momentum]

/-- The zero energy boundary fluxes make total energy exactly conservative. -/
theorem sodQuarterStep_total_energy :
    totalEnergy sodQuarterStep.1 + totalEnergy sodQuarterStep.2 = 11 / 4 := by
  rw [sodQuarterStep_exact]
  change (257 : ℝ) / 128 + 95 / 128 = 11 / 4
  norm_num

#print axioms twoCellStep_balance
#print axioms transmissiveTwoCellStep_balance
#print axioms sodQuarterStep_exact
#print axioms sodQuarterStep_left_admissible
#print axioms sodQuarterStep_right_admissible

end Project.EulerRusanov.RealStencil
