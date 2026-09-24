import Project.EulerRiemann.FrozenOutwardSide

namespace Project.EulerRiemann.Frozen.OutwardNumerics
open Project.Euler2DDynamicFlux.Model (CheckedFlux rejectedFlux componentCheckedBits)

def fluxCheckedBits (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64) : CheckedFlux :=
  let left := sideCheckedBits rhoL mxL myL energyL
  if left.status == 0 then
    let right := sideCheckedBits rhoR mxR myR energyR
    if right.status == 0 then
      let alpha := if left.speed ≤ right.speed then right.speed else left.speed
      let mass := componentCheckedBits alpha left.massFlux right.massFlux rhoL rhoR
      let momentum := componentCheckedBits alpha left.momentumFlux right.momentumFlux mxL mxR
      let transverse := componentCheckedBits alpha left.transverseFlux right.transverseFlux myL myR
      let energy := componentCheckedBits alpha left.energyFlux right.energyFlux energyL energyR
      if mass.status == 0 && momentum.status == 0 && transverse.status == 0 && energy.status == 0 then
        ⟨0, mass.value, momentum.value, transverse.value, energy.value, alpha⟩
      else rejectedFlux
    else rejectedFlux
  else rejectedFlux

end Project.EulerRiemann.Frozen.OutwardNumerics
