import Project.EulerRiemann.FrozenReconstruction
import Project.EulerRiemann.FrozenOutwardFaceStep

namespace Project.EulerRiemann.Frozen.OutwardNumerics
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DCellStep.Model (CheckedCell rejectedCell)

def reconstructedStepCheckedBits (fuel : Nat) (ratio : UInt64)
    (farLeft left center right farRight : State) : CheckedCell :=
  let leftFaces := Reconstruction.reconstruct fuel farLeft left center
  let centerFaces := Reconstruction.reconstruct fuel left center right
  let rightFaces := Reconstruction.reconstruct fuel center right farRight
  if leftFaces.status == 0 && centerFaces.status == 0 && rightFaces.status == 0 then
    faceStepCheckedBits ratio center leftFaces.right centerFaces.left centerFaces.right rightFaces.left
  else rejectedCell

end Project.EulerRiemann.Frozen.OutwardNumerics
