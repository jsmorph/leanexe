import Project.EulerRiemann.NumericsVectors
import Project.EulerRiemann.NumericsComponentReference

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.Euler2DConservative.Guard (decodedState)
open RealRusanov

theorem flux_component_of_accepted (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64)
    (h : (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).status = 0) (i : Fin 4) :
    let flux := fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR
    let left := sideCheckedBits rhoL mxL myL energyL
    let right := sideCheckedBits rhoR mxR myR energyR
    fluxWords flux i =
      (Project.EulerDynamicFlux.Model.componentCheckedBits flux.alpha
        (sideFluxWords left i) (sideFluxWords right i)
        (stateWords rhoL mxL myL energyL i) (stateWords rhoR mxR myR energyR i)).value := by
  unfold fluxCheckedBits at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all [Project.Euler2DDynamicFlux.Model.rejectedFlux]
  all_goals fin_cases i <;> rfl

theorem interface_reference_error (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (hL : StateBounds M rhoL mxL myL energyL) (hR : StateBounds M rhoR mxR myR energyR) :
    let flux := fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR
    ∀ i, |value (fluxWords flux i) - interfaceFlux (value flux.alpha)
      (decodedState rhoL mxL myL energyL) (decodedState rhoR mxR myR energyR) i| ≤
      304 * arithmeticEpsilon * M^5 := by
  let flux := fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR
  let left := sideCheckedBits rhoL mxL myL energyL
  let right := sideCheckedBits rhoR mxR myR energyR
  obtain ⟨hstatus, _, _, _, _, ha, ba, _⟩ :=
    flux_accepted_of_bounds rhoL mxL myL energyL rhoR mxR myR energyR M hM hMmax hL hR
  dsimp only
  intro i
  obtain ⟨hfL, bfL, efL⟩ := side_vector_bounds rhoL mxL myL energyL M hM hMmax hL i
  obtain ⟨hfR, bfR, efR⟩ := side_vector_bounds rhoR mxR myR energyR M hM hMmax hR i
  obtain ⟨hsL, bsL⟩ := state_words_bounds rhoL mxL myL energyL M hM hL i
  obtain ⟨hsR, bsR⟩ := state_words_bounds rhoR mxR myR energyR M hM hR i
  have er := component_reference_error flux.alpha (sideFluxWords left i) (sideFluxWords right i)
    (stateWords rhoL mxL myL energyL i) (stateWords rhoR mxR myR energyR i) ha hfL hfR hsL hsR
    (physicalFlux (decodedState rhoL mxL myL energyL) i)
    (physicalFlux (decodedState rhoR mxR myR energyR) i) M hM hMmax ba bfL bfR bsL bsR efL efR
  rw [flux_component_of_accepted rhoL mxL myL energyL rhoR mxR myR energyR hstatus i]
  simpa only [state_words_value, interfaceFlux] using er

#print axioms flux_component_of_accepted
#print axioms interface_reference_error
end Project.EulerRiemann.Numerics
