import Project.Euler2DDynamicFlux.Model
import Project.Euler2DConservative.Outputs
import Project.EulerDynamicFlux.Safety

namespace Project.Euler2DDynamicFlux.Safety
open Project.Euler2DConservative.Model
open Project.EulerDynamicFlux.Safety (component_result_finite)

theorem accepted_sides (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : UInt64)
    (h : (Model.fluxCheckedBits rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR).status = 0) :
    (sideCheckedBits rhoL momentumL transverseL energyL).status = 0 ∧
    (sideCheckedBits rhoR momentumR transverseR energyR).status = 0 := by
  unfold Model.fluxCheckedBits at h
  dsimp only at h
  split at h
  · rename_i hl
    split at h
    · rename_i hr
      exact ⟨by simpa using hl, by simpa using hr⟩
    · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem accepted_admissible (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : UInt64)
    (h : (Model.fluxCheckedBits rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR).status = 0) :
    Project.Euler2DConservative.Guard.Admissible
      (Project.Euler2DConservative.Guard.decodedState rhoL momentumL transverseL energyL) ∧
    Project.Euler2DConservative.Guard.Admissible
      (Project.Euler2DConservative.Guard.decodedState rhoR momentumR transverseR energyR) := by
  obtain ⟨hl, hr⟩ := accepted_sides rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR h
  exact ⟨Project.Euler2DConservative.Safety.accepted_admissible _ _ _ _ hl,
    Project.Euler2DConservative.Safety.accepted_admissible _ _ _ _ hr⟩

theorem accepted_fields (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : UInt64)
    (h : (Model.fluxCheckedBits rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR).status = 0) :
    let out := Model.fluxCheckedBits rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR
    CodeLib.IEEE64.Finite out.mass ∧ CodeLib.IEEE64.Finite out.momentum ∧
    CodeLib.IEEE64.Finite out.transverse ∧ CodeLib.IEEE64.Finite out.energy ∧ positiveBits out.alpha = true := by
  generalize hresult : Model.fluxCheckedBits rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR = result at h ⊢
  unfold Model.fluxCheckedBits at hresult
  dsimp only at hresult
  split at hresult
  · rename_i hl
    split at hresult
    · rename_i hr
      by_cases hspeed : (sideCheckedBits rhoL momentumL transverseL energyL).speed ≤
          (sideCheckedBits rhoR momentumR transverseR energyR).speed
      all_goals
        simp only [hspeed, ite_true, ite_false] at hresult
        split at hresult
        · rename_i hcomponents
          subst result
          obtain ⟨hmoments, he⟩ := Bool.and_eq_true_iff.mp hcomponents
          obtain ⟨hnormal, ht⟩ := Bool.and_eq_true_iff.mp hmoments
          obtain ⟨hm, hp⟩ := Bool.and_eq_true_iff.mp hnormal
          refine ⟨component_result_finite _ _ _ _ _ (by simpa using hm),
            component_result_finite _ _ _ _ _ (by simpa using hp),
            component_result_finite _ _ _ _ _ (by simpa using ht),
            component_result_finite _ _ _ _ _ (by simpa using he), ?_⟩
          first
          | exact (Project.Euler2DConservative.Safety.accepted_outputPositive _ _ _ _ (by simpa using hl)).2
          | exact (Project.Euler2DConservative.Safety.accepted_outputPositive _ _ _ _ (by simpa using hr)).2
        · subst result
          exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    · subst result
      exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
  · subst result
    exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

#print axioms accepted_sides
#print axioms accepted_fields
#print axioms accepted_admissible
end Project.Euler2DDynamicFlux.Safety
