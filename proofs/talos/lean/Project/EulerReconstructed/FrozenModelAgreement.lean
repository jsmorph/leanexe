import Project.EulerRiemann.FrozenReconstruction
import Project.EulerRiemann.FrozenOutwardFaceStep
import Project.EulerRiemann.FrozenOutwardMaximum
import Project.EulerRiemann.FrozenOutwardMesh
import Project.EulerRiemann.Reconstruction
import Project.EulerRiemann.OutwardFaceStep
import Project.EulerRiemann.OutwardMaximum
import Project.EulerRiemann.OutwardMesh

namespace Project.EulerReconstructed.Frozen.ModelAgreement
open Project.Euler2DCellStep.Sweep (State)

def faces (value : Project.EulerRiemann.Frozen.Reconstruction.Faces) : Project.EulerRiemann.Reconstruction.Faces :=
  ⟨value.status, value.left, value.right, value.factor⟩

theorem candidate (center delta : State) (factor : UInt64) :
    faces (Project.EulerRiemann.Frozen.Reconstruction.candidate center delta factor) =
      Project.EulerRiemann.Reconstruction.candidate center delta factor := by
  unfold Project.EulerRiemann.Frozen.Reconstruction.candidate Project.EulerRiemann.Reconstruction.candidate
  simp only [show Project.EulerRiemann.Frozen.Reconstruction.scale =
      Project.EulerRiemann.Reconstruction.scale from rfl,
    show Project.EulerRiemann.Frozen.Reconstruction.difference =
      Project.EulerRiemann.Reconstruction.difference from rfl,
    show Project.EulerRiemann.Frozen.Reconstruction.sum =
      Project.EulerRiemann.Reconstruction.sum from rfl,
    show Project.EulerRiemann.Frozen.Reconstruction.finiteState =
      Project.EulerRiemann.Reconstruction.finiteState from rfl,
    show Project.EulerRiemann.Frozen.Reconstruction.admissibleState =
      Project.EulerRiemann.Reconstruction.admissibleState from rfl]
  split <;> rfl

theorem limit (fuel : Nat) (center delta : State) (factor : UInt64) :
    faces (Project.EulerRiemann.Frozen.Reconstruction.limit fuel center delta factor) =
      Project.EulerRiemann.Reconstruction.limit fuel center delta factor := by
  induction fuel generalizing factor with
  | zero => rfl
  | succ fuel ih =>
    simp only [Project.EulerRiemann.Frozen.Reconstruction.limit, Project.EulerRiemann.Reconstruction.limit]
    have hCandidate := candidate center delta factor
    have hStatus := congrArg Project.EulerRiemann.Reconstruction.Faces.status hCandidate
    change (Project.EulerRiemann.Frozen.Reconstruction.candidate center delta factor).status =
      (Project.EulerRiemann.Reconstruction.candidate center delta factor).status at hStatus
    rw [hStatus]
    split <;> first | exact hCandidate | exact ih _

theorem reconstruct (fuel : Nat) (left center right : State) :
    faces (Project.EulerRiemann.Frozen.Reconstruction.reconstruct fuel left center right) =
      Project.EulerRiemann.Reconstruction.reconstruct fuel left center right := by
  have hGuard : Project.EulerRiemann.Frozen.Reconstruction.admissibleState =
      Project.EulerRiemann.Reconstruction.admissibleState := rfl
  have hStatus : (Project.EulerRiemann.Frozen.Reconstruction.slope left center right).status =
      (Project.EulerRiemann.Reconstruction.slope left center right).status := by
    unfold Project.EulerRiemann.Frozen.Reconstruction.slope Project.EulerRiemann.Reconstruction.slope
    simp only [show Project.EulerRiemann.Frozen.Reconstruction.difference =
        Project.EulerRiemann.Reconstruction.difference from rfl,
      show Project.EulerRiemann.Frozen.Reconstruction.finiteState =
        Project.EulerRiemann.Reconstruction.finiteState from rfl]
    split <;> rfl
  have hState : (Project.EulerRiemann.Frozen.Reconstruction.slope left center right).state =
      (Project.EulerRiemann.Reconstruction.slope left center right).state := by
    unfold Project.EulerRiemann.Frozen.Reconstruction.slope Project.EulerRiemann.Reconstruction.slope
    simp only [show Project.EulerRiemann.Frozen.Reconstruction.difference =
        Project.EulerRiemann.Reconstruction.difference from rfl,
      show Project.EulerRiemann.Frozen.Reconstruction.finiteState =
        Project.EulerRiemann.Reconstruction.finiteState from rfl]
    split <;> rfl
  simp only [Project.EulerRiemann.Frozen.Reconstruction.reconstruct,
    Project.EulerRiemann.Reconstruction.reconstruct, hGuard, hStatus, hState]
  split
  · split
    · exact limit fuel center _ _
    · rfl
  · rfl

def cell (value : Project.EulerRiemann.Frozen.Traversal.Cell) : Project.EulerRiemann.Traversal.Cell :=
  ⟨value.index, value.state, value.pressure, value.status⟩

theorem scanCell (acc : Project.ProofKit.F64Outward.Checked) (value : Project.EulerRiemann.Frozen.Traversal.Cell) :
    Project.EulerRiemann.Frozen.OutwardMaximum.scanCell acc value =
      Project.EulerRiemann.OutwardMaximum.scanCell acc (cell value) := rfl

theorem faceStep (ratio : UInt64) (center leftOuter leftInner rightInner rightOuter : State) :
    Project.EulerRiemann.Frozen.OutwardNumerics.faceStepCheckedBits ratio center leftOuter leftInner rightInner rightOuter =
      Project.EulerRiemann.OutwardNumerics.faceStepCheckedBits ratio center leftOuter leftInner rightInner rightOuter := rfl

theorem gridRatio (n : Nat) (dt alpha : UInt64) :
    Project.EulerRiemann.Frozen.OutwardCfl.gridRatioChecked n dt alpha =
      Project.EulerRiemann.OutwardCfl.gridRatioChecked n dt alpha := rfl

#print axioms reconstruct
#print axioms scanCell
#print axioms faceStep
#print axioms gridRatio
end Project.EulerReconstructed.Frozen.ModelAgreement
