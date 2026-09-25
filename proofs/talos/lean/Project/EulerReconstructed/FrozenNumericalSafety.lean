import Project.EulerReconstructed.FrozenTraversalSafety
import Project.EulerReconstruction.Spec
import Project.EulerRiemann.FrozenHyperbolicity
import Project.EulerReconstructed.FrozenModelAgreement

namespace Project.EulerReconstructed.Frozen.Numerics
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (State StateSafe)
open Project.Euler2DConservative.Guard (decodedState)
open Project.Euler2DConservative.RealFlux (eigenvalues velocity soundSpeed)
open Project.EulerRiemann.Frozen.Reconstruction (reconstruct)
open Project.EulerRiemann.Frozen.Hyperbolicity (StateHyperbolic CellsHyperbolic state_hyperbolic cells_hyperbolic)
open Project.EulerRiemann.Frozen.Traversal (Cell accepted)
open Project.EulerRiemann.Frozen.OutwardNumerics (reconstructed_step_parts reconstructed_step_characteristic_courant)
open Traversal (Stencil)

noncomputable def ReconstructionFacts (fuel : Nat) (left center right : State) : Prop :=
  let out := reconstruct fuel left center right
  out.status = 0 ∧ StateSafe out.left ∧ StateSafe out.right ∧
    StateHyperbolic out.left ∧ StateHyperbolic out.right ∧
    Project.EulerReconstruction.Spec.Accuracy fuel left center right (ModelAgreement.faces out) ∧
    Finite out.factor ∧ 0 ≤ value out.factor ∧ value out.factor ≤ 1/2

theorem reconstruction_facts (fuel : Nat) (left center right : State)
    (h : (reconstruct fuel left center right).status = 0) :
    ReconstructionFacts fuel left center right := by
  have hs := Project.EulerRiemann.Frozen.Reconstruction.reconstruct_safe fuel left center right h
  have hModel := ModelAgreement.reconstruct fuel left center right
  have hCurrent : (Project.EulerRiemann.Reconstruction.reconstruct fuel left center right).status = 0 := by
    rw [← hModel]
    exact h
  refine ⟨h, hs.1, hs.2, state_hyperbolic _ hs.1, state_hyperbolic _ hs.2, ?_, ?_⟩
  · rw [hModel]
    exact Project.EulerRiemann.Reconstruction.reconstruct_accuracy fuel left center right hCurrent
  · have hFactor := Project.EulerRiemann.Reconstruction.reconstruct_factor fuel left center right
    rw [← hModel] at hFactor
    exact hFactor

def stencilFaces (fuel : Nat) (input : Stencil) : List State :=
  [(reconstruct fuel input.farLeft input.left input.center).right,
    (reconstruct fuel input.left input.center input.right).left,
    (reconstruct fuel input.left input.center input.right).right,
    (reconstruct fuel input.center input.right input.farRight).left]

noncomputable def characteristicMagnitude (state : State) (i : Fin 4) : ℝ :=
  |eigenvalues (velocity (decodedState state.density state.mx state.my state.energy))
    (soundSpeed (decodedState state.density state.mx state.my state.energy)) i|

noncomputable def StencilFacts (n fuel : Nat) (dt ratio : UInt64) (input : Stencil) : Prop :=
  ReconstructionFacts fuel input.farLeft input.left input.center ∧
    ReconstructionFacts fuel input.left input.center input.right ∧
    ReconstructionFacts fuel input.center input.right input.farRight ∧
    ∀ face ∈ stencilFaces fuel input, ∀ i : Fin 4,
      value ratio * characteristicMagnitude face i ≤ 1/2 ∧
        value dt * (n : ℝ) * characteristicMagnitude face i ≤ 1/2

theorem stencil_facts (n fuel : Nat) (dt ratio : UInt64) (input : Stencil)
    (hr : value dt * (n : ℝ) ≤ value ratio)
    (ha : (Project.EulerRiemann.Frozen.OutwardNumerics.reconstructedStepCheckedBits fuel ratio
      input.farLeft input.left input.center input.right input.farRight).status = 0) :
    StencilFacts n fuel dt ratio input := by
  have hp := reconstructed_step_parts fuel ratio input.farLeft input.left input.center input.right input.farRight ha
  refine ⟨reconstruction_facts fuel _ _ _ hp.1, reconstruction_facts fuel _ _ _ hp.2.1,
    reconstruction_facts fuel _ _ _ hp.2.2.1, ?_⟩
  intro face hf i
  have hc := reconstructed_step_characteristic_courant fuel ratio
    input.farLeft input.left input.center input.right input.farRight face ha hf i
  exact ⟨hc, (mul_le_mul_of_nonneg_right hr (abs_nonneg _)).trans hc⟩

noncomputable def SweepFacts (n fuel : Nat) (dt ratio : UInt64) (axis : Bool)
    (grid : Array Cell) : Prop :=
  CellsHyperbolic (Traversal.sweep n fuel axis ratio grid) ∧
    ∀ k (hk : k < grid.size), StencilFacts n fuel dt ratio (Traversal.cellStencil n axis grid grid[k])

theorem sweep_facts (n fuel : Nat) (dt ratio : UInt64) (axis : Bool) (grid : Array Cell)
    (hr : value dt * (n : ℝ) ≤ value ratio)
    (ha : accepted (Traversal.sweep n fuel axis ratio grid) = true) :
    SweepFacts n fuel dt ratio axis grid := by
  refine ⟨cells_hyperbolic _ (Traversal.sweep_safe n fuel axis ratio grid ha), ?_⟩
  intro k hk
  have hCell := Array.all_eq_true.mp ha k (by simpa only [Traversal.sweep_size] using hk)
  have hs : (Traversal.updateCell n fuel axis ratio grid grid[k]).status = 0 := by
    simpa only [Traversal.sweep, Array.getElem_map, beq_iff_eq] using hCell
  exact stencil_facts n fuel dt ratio _ hr hs

#print axioms reconstruction_facts
#print axioms stencil_facts
#print axioms sweep_facts
end Project.EulerReconstructed.Frozen.Numerics
