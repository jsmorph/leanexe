import Project.EulerDynamicFlux.Model

namespace Project.EulerCellStep.Model
open Project.EulerConservative.Model (positiveBits finiteBits sideCheckedBits)
open Project.EulerDynamicFlux.Model (CheckedComponent rejectedComponent fluxCheckedBits)

structure CheckedCell where
  status : UInt64
  density : UInt64
  momentum : UInt64
  energy : UInt64
  pressure : UInt64
  alpha : UInt64
  courant : UInt64
  deriving DecidableEq, Inhabited, Repr

def rejectedCell : CheckedCell := ⟨1, 0, 0, 0, 0, 0, 0⟩

/-- One conservative update, retaining the specified subtraction/multiply order. -/
def updateCheckedBits (ratio state fluxL fluxR : UInt64) : CheckedComponent :=
  if positiveBits ratio && finiteBits state && finiteBits fluxL && finiteBits fluxR then
    let difference := Wasm.IEEE64.sub fluxR fluxL
    let increment := Wasm.IEEE64.mul ratio difference
    let value := Wasm.IEEE64.sub state increment
    if finiteBits difference && finiteBits increment && finiteBits value then
      ⟨0, value⟩
    else rejectedComponent
  else rejectedComponent

/-- Advance the center state with its two dynamic Rusanov interfaces.
The checked CFL ceiling is 1/2; the runner targets 0.45 with rounding headroom. -/
def cellCheckedBits (ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR : UInt64) : CheckedCell :=
  if positiveBits ratio then
    let left := fluxCheckedBits rhoL momentumL energyL rho momentum energy
    if left.status == 0 then
      let right := fluxCheckedBits rho momentum energy rhoR momentumR energyR
      if right.status == 0 then
        let alpha := if left.alpha ≤ right.alpha then right.alpha else left.alpha
        let courant := Wasm.IEEE64.mul ratio alpha
        if positiveBits courant && decide (courant ≤ 0x3FE0000000000000) then
          let nextDensity := updateCheckedBits ratio rho left.mass right.mass
          let nextMomentum := updateCheckedBits ratio momentum left.momentum right.momentum
          let nextEnergy := updateCheckedBits ratio energy left.energy right.energy
          if nextDensity.status == 0 && nextMomentum.status == 0 && nextEnergy.status == 0 then
            let nextSide := sideCheckedBits nextDensity.value nextMomentum.value nextEnergy.value
            if nextSide.status == 0 then
              ⟨0, nextDensity.value, nextMomentum.value, nextEnergy.value, nextSide.pressure, alpha, courant⟩
            else rejectedCell
          else rejectedCell
        else rejectedCell
      else rejectedCell
    else rejectedCell
  else rejectedCell

end Project.EulerCellStep.Model
