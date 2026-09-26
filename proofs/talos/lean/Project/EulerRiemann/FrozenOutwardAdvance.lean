import Project.EulerRiemann.FrozenOutwardSide
import Project.ProofKit.F64Outward

namespace Project.EulerRiemann.Frozen.OutwardNumerics
open Project.Euler2DConservative.Model (positiveBits)
open Project.Euler2DDynamicFlux.Model (CheckedFlux)
open Project.Euler2DCellStep.Model (CheckedCell rejectedCell updateCheckedBits)

def advanceCheckedBits (ratio rho momentum transverse energy : UInt64)
    (left right : CheckedFlux) : CheckedCell :=
  if positiveBits ratio && left.status == 0 && right.status == 0 then
    let alpha := if left.alpha ≤ right.alpha then right.alpha else left.alpha
    if positiveBits alpha then
      let courant := Project.ProofKit.F64Outward.mul true ratio alpha
      if courant.status == 0 && decide (courant.value ≤ 0x3FE0000000000000) then
        let nextDensity := updateCheckedBits ratio rho left.mass right.mass
        let nextMomentum := updateCheckedBits ratio momentum left.momentum right.momentum
        let nextTransverse := updateCheckedBits ratio transverse left.transverse right.transverse
        let nextEnergy := updateCheckedBits ratio energy left.energy right.energy
        if nextDensity.status == 0 && nextMomentum.status == 0 &&
            nextTransverse.status == 0 && nextEnergy.status == 0 then
          let nextSide := sideCheckedBits nextDensity.value nextMomentum.value
            nextTransverse.value nextEnergy.value
          if nextSide.status == 0 then
            ⟨0, nextDensity.value, nextMomentum.value, nextTransverse.value,
              nextEnergy.value, nextSide.pressure, alpha, courant.value⟩
          else rejectedCell
        else rejectedCell
      else rejectedCell
    else rejectedCell
  else rejectedCell

end Project.EulerRiemann.Frozen.OutwardNumerics
