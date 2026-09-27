import CodeLib.IEEE64.Operations

/-!
# Pure model for the guarded Euler--Rusanov entry

This module contains no appeal to Lean's native `Float` evaluator.  The bit
model uses Talos's pure `Wasm.IEEE64` operations in exactly the associations
used by the generated `func0`: pressure multiples are formed from dyadic
multiplications and additions, and `7 / 8` of each conservative-state jump is
formed as `1 / 2 + 1 / 4 + 1 / 8` of that jump.

The independent real model at the end states the mathematical one-dimensional
ideal-gas Euler flux and the fixed-speed Rusanov flux.  It deliberately does
not identify a native Lean floating-point computation with either model.
-/

namespace Project.EulerRusanov.Model

open Wasm

/-! ## Raw-word domain -/

/-- Binary64 encoding of the admitted minimum density, `1 / 8`. -/
def rhoMinBits : UInt64 := 0x3FC0000000000000

/-- Binary64 encoding of the admitted maximum density, `1`. -/
def rhoMaxBits : UInt64 := 0x3FF0000000000000

/-- Binary64 encoding of the admitted minimum pressure, `1 / 16`. -/
def pressureMinBits : UInt64 := 0x3FB0000000000000

/-- Binary64 encoding of the admitted maximum velocity magnitude, `1 / 2`. -/
def velocityMaxBits : UInt64 := 0x3FE0000000000000

/-- Mask that removes the binary64 sign bit. -/
def magnitudeMask : UInt64 := 0x7FFFFFFFFFFFFFFF

/-- Binary64 sign mask, also used to negate finite admitted operands. -/
def signMask : UInt64 := 0x8000000000000000

/-- Binary64 encoding of `1 / 2`. -/
def halfBits : UInt64 := 0x3FE0000000000000

/-- Binary64 encoding of `1 / 4`. -/
def quarterBits : UInt64 := 0x3FD0000000000000

/-- Binary64 encoding of `1 / 8`. -/
def eighthBits : UInt64 := 0x3FC0000000000000

/-- The magnitude word used by the source's integer-only velocity test. -/
def magnitudeBits (bits : UInt64) : UInt64 := bits &&& magnitudeMask

/-- Raw-word density interval check.  Unsigned word ordering agrees with
numeric ordering because both endpoints and every admitted density are
positive finite binary64 encodings. -/
def densityGuard (rho : UInt64) : Bool :=
  decide (rhoMinBits ≤ rho) && decide (rho ≤ rhoMaxBits)

/-- Raw-word pressure interval check, including the source's `p <= rho`
constraint. -/
def pressureGuard (rho p : UInt64) : Bool :=
  decide (pressureMinBits ≤ p) && decide (p ≤ rho)

/-- Raw-word sign-insensitive velocity bound. -/
def velocityGuard (u : UInt64) : Bool :=
  decide (magnitudeBits u ≤ velocityMaxBits)

/-- Domain predicate for one primitive state. -/
def stateGuard (rho u p : UInt64) : Bool :=
  densityGuard rho && pressureGuard rho p && velocityGuard u

/-- Exact Boolean domain predicate of the source entry, in source argument
order `(rhoL, uL, pL, rhoR, uR, pR)`. -/
def eulerGuard
    (rhoL uL pL rhoR uR pR : UInt64) : Bool :=
  decide (rhoMinBits ≤ rhoL) && decide (rhoL ≤ rhoMaxBits) &&
    decide (pressureMinBits ≤ pL) && decide (pL ≤ rhoL) &&
    decide (magnitudeBits uL ≤ velocityMaxBits) &&
    decide (rhoMinBits ≤ rhoR) && decide (rhoR ≤ rhoMaxBits) &&
    decide (pressureMinBits ≤ pR) && decide (pR ≤ rhoR) &&
    decide (magnitudeBits uR ≤ velocityMaxBits)

/-! ## Exact pure binary64 evaluation -/

/-- Every rounded quantity computed for one side before the two states are
combined.  The field dependencies expose the generated program's evaluation
order to later execution and numerical proofs. -/
structure SideBits where
  mass : UInt64
  velocitySquaredMass : UInt64
  halfKinetic : UInt64
  halfPressure : UInt64
  twoPressure : UInt64
  energyPressure : UInt64
  energy : UInt64
  enthalpyPressure : UInt64
  enthalpy : UInt64
  momentumFlux : UInt64
  energyFlux : UInt64
  deriving DecidableEq, Inhabited, Repr

/-- Pure Talos binary64 meaning of the per-side arithmetic in `func0`.
Each `let` matches the corresponding generated local, including the left
association of all additions. -/
def sideBits (rho u p : UInt64) : SideBits :=
  let mass := IEEE64.mul rho u
  let velocitySquaredMass := IEEE64.mul mass u
  let halfKinetic := IEEE64.mul halfBits velocitySquaredMass
  let halfPressure := IEEE64.mul halfBits p
  let twoPressure := IEEE64.add p p
  let energyPressure := IEEE64.add twoPressure halfPressure
  let energy := IEEE64.add energyPressure halfKinetic
  let enthalpyPressure := IEEE64.add energyPressure p
  let enthalpy := IEEE64.add enthalpyPressure halfKinetic
  let momentumFlux := IEEE64.add velocitySquaredMass p
  let energyFlux := IEEE64.mul enthalpy u
  { mass, velocitySquaredMass, halfKinetic, halfPressure, twoPressure,
    energyPressure, energy, enthalpyPressure, enthalpy, momentumFlux,
    energyFlux }

/-- Toggle a binary64 word's sign bit.  On the guarded domain this is exact
real negation; keeping it as a word operation also matches the generated
`i64.xor`. -/
def negateBits (bits : UInt64) : UInt64 := bits ^^^ signMask

/-- Rounded `left - right` in the same add-after-sign-toggle form as `func0`. -/
def jumpBits (left right : UInt64) : UInt64 :=
  IEEE64.add left (negateBits right)

/-- Rounded arithmetic mean used for each physical-flux component. -/
def meanBits (left right : UInt64) : UInt64 :=
  IEEE64.mul halfBits (IEEE64.add left right)

/-- Rounded `7 / 8` scaling in the exact dyadic association emitted for the
source: `(half * x + quarter * x) + eighth * x`. -/
def dissipationBits (jump : UInt64) : UInt64 :=
  IEEE64.add
    (IEEE64.add (IEEE64.mul halfBits jump) (IEEE64.mul quarterBits jump))
    (IEEE64.mul eighthBits jump)

/-- One rounded Rusanov component.  The jump is `stateL - stateR`, so this is
`(fluxL + fluxR) / 2 + (7 / 8) * (stateL - stateR)`. -/
def rusanovComponentBits
    (fluxL fluxR stateL stateR : UInt64) : UInt64 :=
  let jump := jumpBits stateL stateR
  let mean := meanBits fluxL fluxR
  let dissipation := dissipationBits jump
  IEEE64.add mean dissipation

/-- Three binary64 payload words returned by a successful invocation. -/
structure FluxBits where
  mass : UInt64
  momentum : UInt64
  energy : UInt64
  deriving DecidableEq, Inhabited, Repr

/-- Exact pure binary64 result of the accepted branch of generated `func0`.
The three component calls are definitionally the arithmetic performed through
generated locals `32`--`43`. -/
def rusanovBits
    (rhoL uL pL rhoR uR pR : UInt64) : FluxBits :=
  let left := sideBits rhoL uL pL
  let right := sideBits rhoR uR pR
  { mass := rusanovComponentBits left.mass right.mass rhoL rhoR
    momentum := rusanovComponentBits
      left.momentumFlux right.momentumFlux left.mass right.mass
    energy := rusanovComponentBits
      left.energyFlux right.energyFlux left.energy right.energy }

/-- Four public words of the total guarded function. -/
structure CheckedFluxBits where
  status : UInt64
  mass : UInt64
  momentum : UInt64
  energy : UInt64
  deriving DecidableEq, Inhabited, Repr

/-- Total pure result model.  Rejection performs no modeled floating-point
arithmetic and returns status one followed by three positive-zero words. -/
def checkedFluxBitsModel
    (rhoL uL pL rhoR uR pR : UInt64) : CheckedFluxBits :=
  if eulerGuard rhoL uL pL rhoR uR pR then
    let flux := rusanovBits rhoL uL pL rhoR uR pR
    { status := 0, mass := flux.mass, momentum := flux.momentum,
      energy := flux.energy }
  else
    { status := 1, mass := 0, momentum := 0, energy := 0 }

/-- Guarded status word. -/
def statusModel (rhoL uL pL rhoR uR pR : UInt64) : UInt64 :=
  (checkedFluxBitsModel rhoL uL pL rhoR uR pR).status

/-- Guarded mass-flux word. -/
def massResultModel (rhoL uL pL rhoR uR pR : UInt64) : UInt64 :=
  (checkedFluxBitsModel rhoL uL pL rhoR uR pR).mass

/-- Guarded momentum-flux word. -/
def momentumResultModel (rhoL uL pL rhoR uR pR : UInt64) : UInt64 :=
  (checkedFluxBitsModel rhoL uL pL rhoR uR pR).momentum

/-- Guarded energy-flux word. -/
def energyResultModel (rhoL uL pL rhoR uR pR : UInt64) : UInt64 :=
  (checkedFluxBitsModel rhoL uL pL rhoR uR pR).energy

/-- Public words in the source structure's field order. -/
def resultWords (rhoL uL pL rhoR uR pR : UInt64) : List UInt64 :=
  let result := checkedFluxBitsModel rhoL uL pL rhoR uR pR
  [result.status, result.mass, result.momentum, result.energy]

/-- Final interpreter value stack for generated `func0`.  Talos represents
the top of the WebAssembly stack first, hence this is the reverse of the
source structure field order. -/
def resultValues (rhoL uL pL rhoR uR pR : UInt64) : List Wasm.Value :=
  let result := checkedFluxBitsModel rhoL uL pL rhoR uR pR
  [.i64 result.energy, .i64 result.momentum, .i64 result.mass,
    .i64 result.status]

/-! ## Independent exact-real Euler model -/

/-- A one-dimensional primitive ideal-gas state. -/
structure PrimitiveReal where
  rho : ℝ
  velocity : ℝ
  pressure : ℝ

/-- Conservative variables `(rho, rho*u, E)`. -/
structure ConservativeReal where
  density : ℝ
  momentum : ℝ
  energy : ℝ

/-- Components of a one-dimensional Euler numerical flux. -/
structure FluxReal where
  mass : ℝ
  momentum : ℝ
  energy : ℝ

/-- Ideal-gas heat-capacity ratio used by the artifact. -/
noncomputable def gammaReal : ℝ := 7 / 5

/-- Fixed certified signal-speed bound used by the artifact. -/
noncomputable def alphaReal : ℝ := 7 / 4

/-- Decode three raw binary64 words into a mathematical primitive state. -/
noncomputable def primitiveRealOfBits
    (rho u p : UInt64) : PrimitiveReal :=
  { rho := CodeLib.IEEE64.value rho
    velocity := CodeLib.IEEE64.value u
    pressure := CodeLib.IEEE64.value p }

/-- Exact conservative state for `gamma = 7 / 5`, so
`E = (5 / 2) p + (1 / 2) rho u^2`. -/
noncomputable def conservativeReal (state : PrimitiveReal) : ConservativeReal :=
  let velocitySquaredMass := (state.rho * state.velocity) * state.velocity
  { density := state.rho
    momentum := state.rho * state.velocity
    energy := (5 / 2) * state.pressure +
      (1 / 2) * velocitySquaredMass }

/-- Exact physical one-dimensional Euler flux for `gamma = 7 / 5`. -/
noncomputable def eulerFluxReal (state : PrimitiveReal) : FluxReal :=
  let velocitySquaredMass := (state.rho * state.velocity) * state.velocity
  let energy := (5 / 2) * state.pressure +
    (1 / 2) * velocitySquaredMass
  { mass := state.rho * state.velocity
    momentum := velocitySquaredMass + state.pressure
    energy := (energy + state.pressure) * state.velocity }

/-- Exact fixed-speed Rusanov flux.  The sign convention matches
`rusanovBits`: mean physical flux plus `alpha / 2` times `U_L - U_R`. -/
noncomputable def rusanovReal
    (left right : PrimitiveReal) : FluxReal :=
  let stateL := conservativeReal left
  let stateR := conservativeReal right
  let fluxL := eulerFluxReal left
  let fluxR := eulerFluxReal right
  { mass := (1 / 2) * (fluxL.mass + fluxR.mass) +
      (7 / 8) * (stateL.density - stateR.density)
    momentum := (1 / 2) * (fluxL.momentum + fluxR.momentum) +
      (7 / 8) * (stateL.momentum - stateR.momentum)
    energy := (1 / 2) * (fluxL.energy + fluxR.energy) +
      (7 / 8) * (stateL.energy - stateR.energy) }

/-- Exact real Rusanov target associated with six raw input words. -/
noncomputable def rusanovRealOfBits
    (rhoL uL pL rhoR uR pR : UInt64) : FluxReal :=
  rusanovReal (primitiveRealOfBits rhoL uL pL)
    (primitiveRealOfBits rhoR uR pR)

end Project.EulerRusanov.Model
