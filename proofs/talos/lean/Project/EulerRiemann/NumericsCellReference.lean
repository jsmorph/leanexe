import Project.EulerRiemann.NumericsInterfaceReference
import Project.EulerRiemann.NumericsUpdateReference

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.Euler2DConservative.Guard (decodedState)
open RealRusanov

theorem cell_component_error (ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (hr : positiveBits ratio = true) (br : value ratio ≤ 1)
    (hL : StateBounds M rhoL mxL myL energyL) (hC : StateBounds M rho mx my energy)
    (hR : StateBounds M rhoR mxR myR energyR) :
    let left := fluxCheckedBits rhoL mxL myL energyL rho mx my energy
    let right := fluxCheckedBits rho mx my energy rhoR mxR myR energyR
    let reference := update (value ratio) (value left.alpha) (value right.alpha)
      (decodedState rhoL mxL myL energyL) (decodedState rho mx my energy) (decodedState rhoR mxR myR energyR)
    ∀ i,
      let component := Project.EulerCellStep.Model.updateCheckedBits ratio
        (stateWords rho mx my energy i) (fluxWords left i) (fluxWords right i)
      component.status = 0 ∧ Finite component.value ∧
        |value component.value - reference i| ≤
          arithmeticEpsilon * M + 1004 * arithmeticEpsilon * value ratio * M^5 +
            2 * multiplicationUnderflowEpsilon := by
  let left := fluxCheckedBits rhoL mxL myL energyL rho mx my energy
  let right := fluxCheckedBits rho mx my energy rhoR mxR myR energyR
  dsimp only
  intro i
  obtain ⟨hl, bl⟩ := flux_vector_bounds rhoL mxL myL energyL rho mx my energy M hM hMmax hL hC i
  obtain ⟨hh, bh⟩ := flux_vector_bounds rho mx my energy rhoR mxR myR energyR M hM hMmax hC hR i
  obtain ⟨hs, bs⟩ := state_words_bounds rho mx my energy M hM hC i
  have el := interface_reference_error rhoL mxL myL energyL rho mx my energy M hM hMmax hL hC i
  have eh := interface_reference_error rho mx my energy rhoR mxR myR energyR M hM hMmax hC hR i
  have er := update_reference_error ratio (stateWords rho mx my energy i) (fluxWords left i) (fluxWords right i)
    hr hs hl hh br
    (interfaceFlux (value left.alpha) (decodedState rhoL mxL myL energyL) (decodedState rho mx my energy) i)
    (interfaceFlux (value right.alpha) (decodedState rho mx my energy) (decodedState rhoR mxR myR energyR) i)
    M hM hMmax bs bl bh el eh
  simpa only [state_words_value, update] using er

#print axioms cell_component_error
end Project.EulerRiemann.Numerics
