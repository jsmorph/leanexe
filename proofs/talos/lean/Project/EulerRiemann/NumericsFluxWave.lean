import Project.EulerRiemann.NumericsSideWave
import Project.ProofKit.F64Maximum

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order

theorem flux_alpha_of_accepted (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64)
    (h : (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).status = 0) :
    let left := sideCheckedBits rhoL mxL myL energyL
    let right := sideCheckedBits rhoR mxR myR energyR
    (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).alpha =
      if left.speed ≤ right.speed then right.speed else left.speed := by
  unfold fluxCheckedBits at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all [Project.Euler2DDynamicFlux.Model.rejectedFlux]

theorem flux_speed_lower (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (hL : StateBounds M rhoL mxL myL energyL) (hR : StateBounds M rhoR mxR myR energyR) :
    let IL := value energyL - ((value mxL)^2 + (value myL)^2) / (2 * value rhoL)
    let IR := value energyR - ((value mxR)^2 + (value myR)^2) / (2 * value rhoR)
    let cL := Real.sqrt ((14 / 25) * (IL / value rhoL))
    let cR := Real.sqrt ((14 / 25) * (IR / value rhoR))
    let alpha := (fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR).alpha
    |value mxL / value rhoL| + cL / 2 ≤ value alpha ∧
      |value mxR / value rhoR| + cR / 2 ≤ value alpha := by
  let left := sideCheckedBits rhoL mxL myL energyL
  let right := sideCheckedBits rhoR mxR myR energyR
  have hl := (side_accepted_of_bounds rhoL mxL myL energyL hL.finiteDensity hL.finiteMomentum
    hL.finiteTransverse hL.finiteEnergy M hM hMmax hL.densityLower hL.densityUpper
    hL.momentumBound hL.transverseBound hL.energyBound hL.internalMargin hL.guard).2.1
  have hr := (side_accepted_of_bounds rhoR mxR myR energyR hR.finiteDensity hR.finiteMomentum
    hR.finiteTransverse hR.finiteEnergy M hM hMmax hR.densityLower hR.densityUpper
    hR.momentumBound hR.transverseBound hR.energyBound hR.internalMargin hR.guard).2.1
  have hmax := (positive_max_value left.speed right.speed hl hr).2
  have hstatus := (flux_accepted_of_bounds rhoL mxL myL energyL rhoR mxR myR energyR M hM hMmax hL hR).1
  dsimp only
  rw [flux_alpha_of_accepted rhoL mxL myL energyL rhoR mxR myR energyR hstatus, hmax]
  exact ⟨(side_speed_lower rhoL mxL myL energyL M hM hMmax hL).trans (le_max_left _ _),
    (side_speed_lower rhoR mxR myR energyR M hM hMmax hR).trans (le_max_right _ _)⟩

#print axioms flux_alpha_of_accepted
#print axioms flux_speed_lower
end Project.EulerRiemann.Numerics
