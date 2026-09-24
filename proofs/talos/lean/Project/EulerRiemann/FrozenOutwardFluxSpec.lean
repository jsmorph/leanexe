import Project.EulerRiemann.FrozenOutwardFlux
import Project.EulerRiemann.FrozenOutwardSideSpec
import Project.EulerRiemann.FrozenNumericsVectors

namespace Project.EulerRiemann.Frozen.OutwardNumerics
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DDynamicFlux.Model (rejectedFlux)
open Numerics (sideFluxWords stateWords fluxWords)

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
  generalize sideCheckedBits rhoL mxL myL energyL = left at h ⊢
  generalize sideCheckedBits rhoR mxR myR energyR = right at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all [rejectedFlux]
  all_goals fin_cases i <;> tauto

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
  split_ifs at h ⊢ <;> simp_all [rejectedFlux]
  all_goals fin_cases i <;> rfl

theorem flux_alpha_of_accepted (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64)
    (h : (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).status = 0) :
    let left := sideCheckedBits rhoL mxL myL energyL
    let right := sideCheckedBits rhoR mxR myR energyR
    (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).alpha =
      if left.speed ≤ right.speed then right.speed else left.speed := by
  unfold fluxCheckedBits at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all [rejectedFlux]

theorem flux_bounds (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64)
    (h : (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).status = 0) :
    let alpha := (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).alpha
    Finite alpha ∧ 0 < value alpha ∧
      OutwardMaximum.Bounds (⟨rhoL, mxL, myL, energyL⟩ : State) alpha ∧
      OutwardMaximum.Bounds (⟨rhoR, mxR, myR, energyR⟩ : State) alpha := by
  obtain ⟨hL, hR, _⟩ := accepted_interface_parts rhoL mxL myL energyL rhoR mxR myR energyR h 0
  have hb := Project.EulerDynamicFlux.Safety.selected_speed_bound _ _
    (side_speed_positive rhoL mxL myL energyL hL)
    (side_speed_positive rhoR mxR myR energyR hR)
  dsimp only
  rw [flux_alpha_of_accepted rhoL mxL myL energyL rhoR mxR myR energyR h]
  exact ⟨hb.1, hb.2.1,
    OutwardMaximum.bounds_mono (side_bounds rhoL mxL myL energyL hL) hb.2.2.1,
    OutwardMaximum.bounds_mono (side_bounds rhoR mxR myR energyR hR) hb.2.2.2⟩

theorem flux_finite (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64)
    (h : (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).status = 0) (i : Fin 4) :
    Finite (fluxWords (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR) i) := by
  rw [flux_component_of_accepted rhoL mxL myL energyL rhoR mxR myR energyR h i]
  exact Project.EulerDynamicFlux.Safety.component_result_finite _ _ _ _ _
    (accepted_interface_parts rhoL mxL myL energyL rhoR mxR myR energyR h i).2.2

theorem flux_result (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64) :
    fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR = rejectedFlux ∨
      (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).status = 0 := by
  unfold fluxCheckedBits
  dsimp only
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem flux_behavior (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64) :
    let flux := fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR
    flux = rejectedFlux ∨ flux.status = 0 ∧
      Finite flux.alpha ∧ 0 < value flux.alpha ∧
      OutwardMaximum.Bounds (⟨rhoL, mxL, myL, energyL⟩ : State) flux.alpha ∧
      OutwardMaximum.Bounds (⟨rhoR, mxR, myR, energyR⟩ : State) flux.alpha ∧
      ∀ i : Fin 4, Finite (fluxWords flux i) := by
  rcases flux_result rhoL mxL myL energyL rhoR mxR myR energyR with hr | hs
  · exact Or.inl hr
  · obtain ⟨hf, hp, hL, hR⟩ := flux_bounds rhoL mxL myL energyL rhoR mxR myR energyR hs
    exact Or.inr ⟨hs, hf, hp, hL, hR, flux_finite rhoL mxL myL energyL rhoR mxR myR energyR hs⟩

#print axioms accepted_interface_parts
#print axioms flux_component_of_accepted
#print axioms flux_alpha_of_accepted
#print axioms flux_bounds
#print axioms flux_finite
#print axioms flux_behavior
end Project.EulerRiemann.Frozen.OutwardNumerics
