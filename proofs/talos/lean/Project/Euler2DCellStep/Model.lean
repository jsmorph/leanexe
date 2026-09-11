import Project.Euler2DDynamicFlux.Model
import Project.EulerCellStep.Model

namespace Project.Euler2DCellStep.Model
open Project.Euler2DConservative.Model (positiveBits finiteBits sideCheckedBits)
open Project.Euler2DDynamicFlux.Model (CheckedComponent fluxCheckedBits)

abbrev updateCheckedBits (ratio state fluxL fluxR : UInt64) :=
  Project.EulerCellStep.Model.updateCheckedBits ratio state fluxL fluxR

structure CheckedCell where
  status : UInt64
  density : UInt64
  momentum : UInt64
  transverse : UInt64
  energy : UInt64
  pressure : UInt64
  alpha : UInt64
  courant : UInt64
  deriving DecidableEq, Inhabited, Repr

def rejectedCell : CheckedCell := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

/-- Advance the center state with its two dynamic Rusanov interfaces.
The checked CFL ceiling is 1/2; the runner targets 0.4 in each direction with rounding headroom. -/
def cellCheckedBits (ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR : UInt64) : CheckedCell :=
  if positiveBits ratio then
    let left := fluxCheckedBits rhoL momentumL transverseL energyL rho momentum transverse energy
    if left.status == 0 then
      let right := fluxCheckedBits rho momentum transverse energy rhoR momentumR transverseR energyR
      if right.status == 0 then
        let alpha := if left.alpha ≤ right.alpha then right.alpha else left.alpha
        let courant := Wasm.IEEE64.mul ratio alpha
        if positiveBits courant && decide (courant ≤ 0x3FE0000000000000) then
          let nextDensity := updateCheckedBits ratio rho left.mass right.mass
          let nextMomentum := updateCheckedBits ratio momentum left.momentum right.momentum
          let nextTransverse := updateCheckedBits ratio transverse left.transverse right.transverse
          let nextEnergy := updateCheckedBits ratio energy left.energy right.energy
          if nextDensity.status == 0 && nextMomentum.status == 0 && nextTransverse.status == 0 && nextEnergy.status == 0 then
            let nextSide := sideCheckedBits nextDensity.value nextMomentum.value nextTransverse.value nextEnergy.value
            if nextSide.status == 0 then
              ⟨0, nextDensity.value, nextMomentum.value, nextTransverse.value, nextEnergy.value, nextSide.pressure, alpha, courant⟩
            else rejectedCell
          else rejectedCell
        else rejectedCell
      else rejectedCell
    else rejectedCell
  else rejectedCell

end Project.Euler2DCellStep.Model
