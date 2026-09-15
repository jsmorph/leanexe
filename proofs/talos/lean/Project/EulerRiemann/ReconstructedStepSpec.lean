import Project.EulerRiemann.ReconstructedStep
import Project.EulerRiemann.ReconstructionSafety
import Project.EulerRiemann.OutwardFaceStepSpec

namespace Project.EulerRiemann.OutwardNumerics
open Project.Euler2DCellStep.Sweep (State StateSafe)
open Project.Euler2DCellStep.Model (rejectedCell)
open Project.Euler2DConservative.Guard (StateBounds decodedState)
open Project.Euler2DConservative.RealFlux (eigenvalues velocity soundSpeed)
open CodeLib.IEEE64

theorem reconstructed_step_parts (fuel : Nat) (ratio : UInt64)
    (farLeft left center right farRight : State)
    (h : (reconstructedStepCheckedBits fuel ratio farLeft left center right farRight).status = 0) :
    let lf := Reconstruction.reconstruct fuel farLeft left center
    let cf := Reconstruction.reconstruct fuel left center right
    let rf := Reconstruction.reconstruct fuel center right farRight
    lf.status = 0 ∧ cf.status = 0 ∧ rf.status = 0 ∧
      reconstructedStepCheckedBits fuel ratio farLeft left center right farRight =
        faceStepCheckedBits ratio center lf.right cf.left cf.right rf.left := by
  unfold reconstructedStepCheckedBits at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hg
  · have hs : (Reconstruction.reconstruct fuel farLeft left center).status = 0 ∧
        (Reconstruction.reconstruct fuel left center right).status = 0 ∧
        (Reconstruction.reconstruct fuel center right farRight).status = 0 := by
      simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using hg
    exact ⟨hs.1, hs.2.1, hs.2.2, rfl⟩
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem reconstructed_step_result (fuel : Nat) (ratio : UInt64)
    (farLeft left center right farRight : State) :
    reconstructedStepCheckedBits fuel ratio farLeft left center right farRight = rejectedCell ∨
      (reconstructedStepCheckedBits fuel ratio farLeft left center right farRight).status = 0 := by
  unfold reconstructedStepCheckedBits
  dsimp only
  split_ifs
  · exact (face_step_behavior ratio center _ _ _ _).imp_right (fun h => h.1)
  · exact Or.inl rfl

theorem reconstructed_step_state (fuel : Nat) (ratio : UInt64)
    (farLeft left center right farRight : State)
    (h : (reconstructedStepCheckedBits fuel ratio farLeft left center right farRight).status = 0) :
    let out := reconstructedStepCheckedBits fuel ratio farLeft left center right farRight
    StateBounds out.density out.momentum out.transverse out.energy ∧
      Project.Euler2DConservative.Model.positiveBits out.pressure = true := by
  have hp := reconstructed_step_parts fuel ratio farLeft left center right farRight h
  rw [hp.2.2.2] at h ⊢
  exact advance_state ratio center.density center.mx center.my center.energy _ _ h

theorem reconstructed_step_faces_safe (fuel : Nat) (ratio : UInt64)
    (farLeft left center right farRight : State)
    (h : (reconstructedStepCheckedBits fuel ratio farLeft left center right farRight).status = 0) :
    let lf := Reconstruction.reconstruct fuel farLeft left center
    let cf := Reconstruction.reconstruct fuel left center right
    let rf := Reconstruction.reconstruct fuel center right farRight
    (StateSafe lf.left ∧ StateSafe lf.right) ∧
      (StateSafe cf.left ∧ StateSafe cf.right) ∧ (StateSafe rf.left ∧ StateSafe rf.right) := by
  have hp := reconstructed_step_parts fuel ratio farLeft left center right farRight h
  exact ⟨Reconstruction.reconstruct_safe _ _ _ _ hp.1,
    Reconstruction.reconstruct_safe _ _ _ _ hp.2.1,
    Reconstruction.reconstruct_safe _ _ _ _ hp.2.2.1⟩

theorem reconstructed_step_characteristic_courant (fuel : Nat) (ratio : UInt64)
    (farLeft left center right farRight face : State)
    (h : (reconstructedStepCheckedBits fuel ratio farLeft left center right farRight).status = 0)
    (hf : face ∈ [(Reconstruction.reconstruct fuel farLeft left center).right,
      (Reconstruction.reconstruct fuel left center right).left,
      (Reconstruction.reconstruct fuel left center right).right,
      (Reconstruction.reconstruct fuel center right farRight).left]) (i : Fin 4) :
    value ratio * |eigenvalues
      (velocity (decodedState face.density face.mx face.my face.energy))
      (soundSpeed (decodedState face.density face.mx face.my face.energy)) i| ≤ (1 : ℝ) / 2 := by
  have hp := reconstructed_step_parts fuel ratio farLeft left center right farRight h
  rw [hp.2.2.2] at h
  exact face_step_characteristic_courant ratio center _ _ _ _ h face hf i

#print axioms reconstructed_step_parts
#print axioms reconstructed_step_result
#print axioms reconstructed_step_state
#print axioms reconstructed_step_faces_safe
#print axioms reconstructed_step_characteristic_courant
end Project.EulerRiemann.OutwardNumerics
