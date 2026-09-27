import Project.EulerDynamicFlux.Model
import Project.EulerConservative.Outputs

namespace Project.EulerDynamicFlux.Safety
open Project.EulerConservative.Model
open Project.ProofKit.F64Order (finiteBits_iff)

/-- The six rounded operations in one Rusanov component, in source order. -/
def componentWords (alpha fluxL fluxR stateL stateR : UInt64) : List UInt64 :=
  let sum := Wasm.IEEE64.add fluxL fluxR
  let mean := Wasm.IEEE64.mul 0x3FE0000000000000 sum
  let jump := Wasm.IEEE64.sub stateR stateL
  let viscosity := Wasm.IEEE64.mul alpha jump
  let halfViscosity := Wasm.IEEE64.mul 0x3FE0000000000000 viscosity
  let value := Wasm.IEEE64.sub mean halfViscosity
  [sum, mean, jump, viscosity, halfViscosity, value]

private theorem finite_of_guard {word : UInt64} (h : finiteBits word = true) :
    CodeLib.IEEE64.Finite word := (finiteBits_iff word).mp h

theorem component_intermediates_finite (alpha fluxL fluxR stateL stateR : UInt64)
    (h : (Model.componentCheckedBits alpha fluxL fluxR stateL stateR).status = 0) :
    ∀ word ∈ componentWords alpha fluxL fluxR stateL stateR, CodeLib.IEEE64.Finite word := by
  unfold Model.componentCheckedBits at h
  split at h
  · dsimp only at h
    split at h
    · rename_i hfinite
      obtain ⟨h5, hv⟩ := Bool.and_eq_true_iff.mp hfinite
      obtain ⟨h4, hhalf⟩ := Bool.and_eq_true_iff.mp h5
      obtain ⟨h3, hvisc⟩ := Bool.and_eq_true_iff.mp h4
      obtain ⟨h2, hjump⟩ := Bool.and_eq_true_iff.mp h3
      obtain ⟨hsum, hmean⟩ := Bool.and_eq_true_iff.mp h2
      simp only [componentWords, List.forall_mem_cons]
      exact ⟨finite_of_guard hsum, finite_of_guard hmean, finite_of_guard hjump,
        finite_of_guard hvisc, finite_of_guard hhalf, finite_of_guard hv, List.forall_mem_nil _⟩
    · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem component_result_finite (alpha fluxL fluxR stateL stateR : UInt64)
    (h : (Model.componentCheckedBits alpha fluxL fluxR stateL stateR).status = 0) :
    CodeLib.IEEE64.Finite (Model.componentCheckedBits alpha fluxL fluxR stateL stateR).value := by
  generalize hresult : Model.componentCheckedBits alpha fluxL fluxR stateL stateR = result at h ⊢
  unfold Model.componentCheckedBits at hresult
  split at hresult
  · dsimp only at hresult
    split at hresult
    · rename_i hfinite
      subst result
      exact finite_of_guard (Bool.and_eq_true_iff.mp hfinite).2
    · subst result
      exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
  · subst result
    exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem accepted_sides (rhoL momentumL energyL rhoR momentumR energyR : UInt64)
    (h : (Model.fluxCheckedBits rhoL momentumL energyL rhoR momentumR energyR).status = 0) :
    (sideCheckedBits rhoL momentumL energyL).status = 0 ∧
    (sideCheckedBits rhoR momentumR energyR).status = 0 := by
  unfold Model.fluxCheckedBits at h
  dsimp only at h
  split at h
  · rename_i hl
    split at h
    · rename_i hr
      exact ⟨by simpa using hl, by simpa using hr⟩
    · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem accepted_admissible (rhoL momentumL energyL rhoR momentumR energyR : UInt64)
    (h : (Model.fluxCheckedBits rhoL momentumL energyL rhoR momentumR energyR).status = 0) :
    Project.EulerRusanov.RealConservative.Admissible
      (Project.EulerConservative.Guard.decodedState rhoL momentumL energyL) ∧
    Project.EulerRusanov.RealConservative.Admissible
      (Project.EulerConservative.Guard.decodedState rhoR momentumR energyR) := by
  obtain ⟨hl, hr⟩ := accepted_sides rhoL momentumL energyL rhoR momentumR energyR h
  exact ⟨Project.EulerConservative.Safety.accepted_admissible _ _ _ hl,
    Project.EulerConservative.Safety.accepted_admissible _ _ _ hr⟩

private theorem max_positive (left right : UInt64)
    (hl : positiveBits left = true) (hr : positiveBits right = true) :
    positiveBits (if left ≤ right then right else left) = true := by
  split <;> assumption

/-- Ordering accepted positive words selects a bound on both decoded speeds. -/
theorem selected_speed_bound (left right : UInt64)
    (hl : positiveBits left = true) (hr : positiveBits right = true) :
    let alpha := if left ≤ right then right else left
    CodeLib.IEEE64.Finite alpha ∧ 0 < CodeLib.IEEE64.value alpha ∧
      CodeLib.IEEE64.value left ≤ CodeLib.IEEE64.value alpha ∧
      CodeLib.IEEE64.value right ≤ CodeLib.IEEE64.value alpha := by
  have hpositive := max_positive left right hl hr
  have hspec := Project.ProofKit.F64Order.positiveBits_spec _ hpositive
  refine ⟨hspec.1, hspec.2, ?_⟩
  have positive_le (a b : UInt64) (ha : positiveBits a = true)
      (hb : positiveBits b = true) (hab : a ≤ b) :
      CodeLib.IEEE64.value a ≤ CodeLib.IEEE64.value b := by
    have hm := Project.ProofKit.F64Order.abs_value_mono a b (by
      simpa only [Project.ProofKit.F64Order.absBits_of_positive a ha,
        Project.ProofKit.F64Order.absBits_of_positive b hb] using hab)
    simpa only [abs_of_pos (Project.ProofKit.F64Order.positiveBits_spec a ha).2,
      abs_of_pos (Project.ProofKit.F64Order.positiveBits_spec b hb).2] using hm
  by_cases hle : left ≤ right
  · simp only [hle, ite_true]
    exact ⟨positive_le left right hl hr hle, le_rfl⟩
  · simp only [hle, ite_false]
    refine ⟨le_rfl, positive_le right left hr hl ?_⟩
    exact UInt64.le_iff_toNat_le.mpr (by
      have hn := hle
      simp only [UInt64.le_iff_toNat_le] at hn
      omega)

theorem accepted_fields (rhoL momentumL energyL rhoR momentumR energyR : UInt64)
    (h : (Model.fluxCheckedBits rhoL momentumL energyL rhoR momentumR energyR).status = 0) :
    let out := Model.fluxCheckedBits rhoL momentumL energyL rhoR momentumR energyR
    CodeLib.IEEE64.Finite out.mass ∧ CodeLib.IEEE64.Finite out.momentum ∧
    CodeLib.IEEE64.Finite out.energy ∧ positiveBits out.alpha = true := by
  generalize hresult : Model.fluxCheckedBits rhoL momentumL energyL rhoR momentumR energyR = result at h ⊢
  unfold Model.fluxCheckedBits at hresult
  dsimp only at hresult
  split at hresult
  · rename_i hl
    split at hresult
    · rename_i hr
      by_cases hspeed : (sideCheckedBits rhoL momentumL energyL).speed ≤
          (sideCheckedBits rhoR momentumR energyR).speed
      all_goals
        simp only [hspeed, ite_true, ite_false] at hresult
        split at hresult
        · rename_i hcomponents
          subst result
          obtain ⟨hmoments, he⟩ := Bool.and_eq_true_iff.mp hcomponents
          obtain ⟨hm, hp⟩ := Bool.and_eq_true_iff.mp hmoments
          refine ⟨component_result_finite _ _ _ _ _ (by simpa using hm),
            component_result_finite _ _ _ _ _ (by simpa using hp),
            component_result_finite _ _ _ _ _ (by simpa using he), ?_⟩
          first
          | exact (Project.EulerConservative.Safety.accepted_outputPositive _ _ _ (by simpa using hl)).2
          | exact (Project.EulerConservative.Safety.accepted_outputPositive _ _ _ (by simpa using hr)).2
        · subst result
          exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    · subst result
      exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
  · subst result
    exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

#print axioms component_intermediates_finite
#print axioms component_result_finite
#print axioms accepted_sides
#print axioms selected_speed_bound
#print axioms accepted_fields
#print axioms accepted_admissible
end Project.EulerDynamicFlux.Safety
