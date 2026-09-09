import Project.Euler2DConservative.Model
import Project.EulerDynamicFlux.Model

namespace Project.Euler2DDynamicFlux.Model
open Project.Euler2DConservative.Model

abbrev CheckedComponent := Project.EulerDynamicFlux.Model.CheckedComponent
abbrev componentCheckedBits := Project.EulerDynamicFlux.Model.componentCheckedBits

structure CheckedFlux where
  status : UInt64
  mass : UInt64
  momentum : UInt64
  transverse : UInt64
  energy : UInt64
  alpha : UInt64
  deriving DecidableEq, Inhabited, Repr

def rejectedFlux : CheckedFlux := ⟨1, 0, 0, 0, 0, 0⟩

/-- Both sides must be accepted before their positive speed words are ordered. -/
def fluxCheckedBits (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : UInt64) : CheckedFlux :=
  let left := sideCheckedBits rhoL momentumL transverseL energyL
  if left.status == 0 then
    let right := sideCheckedBits rhoR momentumR transverseR energyR
    if right.status == 0 then
      let alpha := if left.speed ≤ right.speed then right.speed else left.speed
      let mass := componentCheckedBits alpha left.massFlux right.massFlux rhoL rhoR
      let momentum := componentCheckedBits alpha left.momentumFlux right.momentumFlux momentumL momentumR
      let transverse := componentCheckedBits alpha left.transverseFlux right.transverseFlux transverseL transverseR
      let energy := componentCheckedBits alpha left.energyFlux right.energyFlux energyL energyR
      if mass.status == 0 && momentum.status == 0 && transverse.status == 0 && energy.status == 0 then
        ⟨0, mass.value, momentum.value, transverse.value, energy.value, alpha⟩
      else rejectedFlux
    else rejectedFlux
  else rejectedFlux

end Project.Euler2DDynamicFlux.Model
