import LeanExe.Examples.Euler2DDynamicFlux

namespace LeanExe.Examples.Euler2DCellStep
open LeanExe.Examples.Euler2DConservative (positiveBits finiteBits sideCheckedBits)
open LeanExe.Examples.Euler2DDynamicFlux (CheckedComponent rejectedComponent fluxCheckedBits)

structure CheckedCell where
  status : UInt64
  density : UInt64
  momentum : UInt64
  transverse : UInt64
  energy : UInt64
  pressure : UInt64
  alpha : UInt64
  courant : UInt64
  deriving Inhabited

def rejectedCell : CheckedCell := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

/-- One conservative update, retaining the specified subtraction/multiply order. -/
def updateCheckedBits (ratio state fluxL fluxR : UInt64) : CheckedComponent :=
  if positiveBits ratio && finiteBits state && finiteBits fluxL && finiteBits fluxR then
    let difference := LeanExe.Float64.subBits fluxR fluxL
    let increment := LeanExe.Float64.mulBits ratio difference
    let value := LeanExe.Float64.subBits state increment
    if finiteBits difference && finiteBits increment && finiteBits value then
      ⟨0, value⟩
    else rejectedComponent
  else rejectedComponent

/-- Advance the center state with its two dynamic Rusanov interfaces.
The checked CFL ceiling is 1/2; the runner targets 0.4 in each direction with rounding headroom. -/
def cellCheckedBits (ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR : UInt64) : CheckedCell :=
  if positiveBits ratio then
    let left := fluxCheckedBits rhoL momentumL transverseL energyL rho momentum transverse energy
    if left.status == 0 then
      let right := fluxCheckedBits rho momentum transverse energy rhoR momentumR transverseR energyR
      if right.status == 0 then
        let alpha := if left.alpha ≤ right.alpha then right.alpha else left.alpha
        let courant := LeanExe.Float64.mulBits ratio alpha
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

end LeanExe.Examples.Euler2DCellStep
