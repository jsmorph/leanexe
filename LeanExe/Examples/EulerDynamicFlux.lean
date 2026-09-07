import LeanExe.Examples.EulerConservative

namespace LeanExe.Examples.EulerDynamicFlux
open LeanExe.Examples.EulerConservative

structure CheckedComponent where
  status : UInt64
  value : UInt64
  deriving Inhabited

structure CheckedFlux where
  status : UInt64
  mass : UInt64
  momentum : UInt64
  energy : UInt64
  alpha : UInt64
  deriving Inhabited

def rejectedComponent : CheckedComponent := ⟨1, 0⟩
def rejectedFlux : CheckedFlux := ⟨1, 0, 0, 0, 0⟩

/-- One exactly associated Rusanov component, rejecting every nonfinite stage. -/
def componentCheckedBits (alpha fluxL fluxR stateL stateR : UInt64) : CheckedComponent :=
  if positiveBits alpha && finiteBits fluxL && finiteBits fluxR &&
      finiteBits stateL && finiteBits stateR then
    let sum := LeanExe.Float64.addBits fluxL fluxR
    let mean := LeanExe.Float64.mulBits 0x3FE0000000000000 sum
    let jump := LeanExe.Float64.subBits stateR stateL
    let viscosity := LeanExe.Float64.mulBits alpha jump
    let halfViscosity := LeanExe.Float64.mulBits 0x3FE0000000000000 viscosity
    let value := LeanExe.Float64.subBits mean halfViscosity
    if finiteBits sum && finiteBits mean && finiteBits jump &&
        finiteBits viscosity && finiteBits halfViscosity && finiteBits value then
      ⟨0, value⟩
    else rejectedComponent
  else rejectedComponent

/-- Both sides must be accepted before their positive speed words are ordered. -/
def fluxCheckedBits (rhoL momentumL energyL rhoR momentumR energyR : UInt64) : CheckedFlux :=
  let left := sideCheckedBits rhoL momentumL energyL
  if left.status == 0 then
    let right := sideCheckedBits rhoR momentumR energyR
    if right.status == 0 then
      let alpha := if left.speed ≤ right.speed then right.speed else left.speed
      let mass := componentCheckedBits alpha left.massFlux right.massFlux rhoL rhoR
      let momentum := componentCheckedBits alpha left.momentumFlux right.momentumFlux momentumL momentumR
      let energy := componentCheckedBits alpha left.energyFlux right.energyFlux energyL energyR
      if mass.status == 0 && momentum.status == 0 && energy.status == 0 then
        ⟨0, mass.value, momentum.value, energy.value, alpha⟩
      else rejectedFlux
    else rejectedFlux
  else rejectedFlux

end LeanExe.Examples.EulerDynamicFlux
