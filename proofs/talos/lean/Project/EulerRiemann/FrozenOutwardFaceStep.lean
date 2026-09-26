import Project.EulerRiemann.FrozenOutwardFlux
import Project.EulerRiemann.FrozenOutwardAdvance
import Project.Euler2DCellStep.SweepModel

namespace Project.EulerRiemann.Frozen.OutwardNumerics
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DCellStep.Model (CheckedCell)

def faceStepCheckedBits (ratio : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State) : CheckedCell :=
  let left := fluxCheckedBits leftOuter.density leftOuter.mx leftOuter.my leftOuter.energy
    leftInner.density leftInner.mx leftInner.my leftInner.energy
  let right := fluxCheckedBits rightInner.density rightInner.mx rightInner.my rightInner.energy
    rightOuter.density rightOuter.mx rightOuter.my rightOuter.energy
  advanceCheckedBits ratio center.density center.mx center.my center.energy left right

end Project.EulerRiemann.Frozen.OutwardNumerics
