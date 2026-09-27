import Project.EulerRiemann.NumericsSideResidual
import Project.EulerRiemann.NumericsComponentRadius
import Project.EulerRiemann.NumericsInterfaceReference

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.Euler2DConservative.Guard (decodedState)
open RealRusanov
noncomputable section

def sideFluxErrorBounds (rho mx my energy : UInt64) : Fin 4 → ℝ :=
  let bound := sideErrorBounds rho mx my energy
  ![0, bound.momentum, bound.transverse, bound.energy]

theorem accepted_side_vector_residual (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) (i : Fin 4) :
    |value (sideFluxWords (sideCheckedBits rho mx my energy) i) -
      physicalFlux (decodedState rho mx my energy) i| ≤ sideFluxErrorBounds rho mx my energy i := by
  obtain ⟨hmass, _, hnormal, htransverse, henergy⟩ :=
    accepted_side_reference_bound rho mx my energy h
  fin_cases i
  · change |value (sideCheckedBits rho mx my energy).massFlux - value mx| ≤ 0
    rw [hmass, sub_self, abs_zero]
  · exact hnormal
  · exact htransverse
  · exact henergy

theorem accepted_interface_parts (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64)
    (h : (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).status = 0) (i : Fin 4) :
    let flux := fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR
    let left := sideCheckedBits rhoL mxL myL energyL
    let right := sideCheckedBits rhoR mxR myR energyR
    left.status = 0 ∧ right.status = 0 ∧
      (Project.EulerDynamicFlux.Model.componentCheckedBits flux.alpha
        (sideFluxWords left i) (sideFluxWords right i)
        (stateWords rhoL mxL myL energyL i) (stateWords rhoR mxR myR energyR i)).status = 0 := by
  unfold fluxCheckedBits at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all [Project.Euler2DDynamicFlux.Model.rejectedFlux]
  all_goals fin_cases i <;> tauto

def interfaceErrorBounds (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64) (i : Fin 4) : ℝ :=
  let flux := fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR
  let left := sideCheckedBits rhoL mxL myL energyL
  let right := sideCheckedBits rhoR mxR myR energyR
  Project.ProofKit.F64RusanovResidual.errorBound 0x3FE0000000000000 flux.alpha
    (sideFluxWords left i) (sideFluxWords right i)
    (stateWords rhoL mxL myL energyL i) (stateWords rhoR mxR myR energyR i) (fluxWords flux i) +
    (1 / 2) * (sideFluxErrorBounds rhoL mxL myL energyL i + sideFluxErrorBounds rhoR mxR myR energyR i)

theorem accepted_interface_reference_bound (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64)
    (h : (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).status = 0) (i : Fin 4) :
    let flux := fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR
    |value (fluxWords flux i) - interfaceFlux (value flux.alpha)
      (decodedState rhoL mxL myL energyL) (decodedState rhoR mxR myR energyR) i| ≤
      interfaceErrorBounds rhoL mxL myL energyL rhoR mxR myR energyR i := by
  obtain ⟨hL, hR, hComponent⟩ := accepted_interface_parts rhoL mxL myL energyL rhoR mxR myR energyR h i
  have hBound := accepted_component_reference_bound _ _ _ _ _ _ _ _ _ hComponent
    (accepted_side_vector_residual rhoL mxL myL energyL hL i)
    (accepted_side_vector_residual rhoR mxR myR energyR hR i)
  dsimp only [interfaceErrorBounds]
  rw [flux_component_of_accepted rhoL mxL myL energyL rhoR mxR myR energyR h i]
  have hReference : interfaceFlux
      (value (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).alpha)
      (decodedState rhoL mxL myL energyL) (decodedState rhoR mxR myR energyR) i =
      (1 / 2) * (physicalFlux (decodedState rhoL mxL myL energyL) i +
        physicalFlux (decodedState rhoR mxR myR energyR) i -
        value (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).alpha *
          (value (stateWords rhoR mxR myR energyR i) - value (stateWords rhoL mxL myL energyL i))) := by
    rw [state_words_value, state_words_value]
    unfold interfaceFlux
    ring
  rw [hReference]
  exact hBound

#print axioms accepted_side_vector_residual
#print axioms accepted_interface_parts
#print axioms accepted_interface_reference_bound
end
end Project.EulerRiemann.Numerics
