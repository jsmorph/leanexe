import Project.EulerRiemann.Numerics
import Project.Euler2DCellStep.Safety

namespace Project.EulerRiemann.Numerics
open Project.Euler2DConservative.Guard
open Project.Euler2DConservative.Model (positiveBits)

theorem stateGuard_extends (rho mx my energy : UInt64)
    (h : Project.Euler2DConservative.Model.stateGuard rho mx my energy = true) :
    stateGuard rho mx my energy = true := by
  rcases Bool.or_eq_true_iff.mp h with hn | he
  · exact Bool.or_eq_true_iff.mpr (Or.inl hn)
  · exact Bool.or_eq_true_iff.mpr
      (Or.inr (Project.ProofKit.F64AdmissibilityTiny.checked_extends rho mx my energy he))

theorem side_eq_of_old_guard (rho mx my energy : UInt64)
    (h : Project.Euler2DConservative.Model.stateGuard rho mx my energy = true) :
    sideCheckedBits rho mx my energy =
      Project.Euler2DConservative.Model.sideCheckedBits rho mx my energy := by
  simp only [sideCheckedBits, Project.Euler2DConservative.Model.sideCheckedBits,
    stateGuard_extends rho mx my energy h, h, ite_true]

theorem side_eq_of_old_accepted (rho mx my energy : UInt64)
    (h : (Project.Euler2DConservative.Model.sideCheckedBits rho mx my energy).status = 0) :
    sideCheckedBits rho mx my energy =
      Project.Euler2DConservative.Model.sideCheckedBits rho mx my energy :=
  side_eq_of_old_guard rho mx my energy
    (Project.Euler2DConservative.Safety.accepted_inputGuard rho mx my energy h)

theorem stateGuard_spec (rho mx my energy : UInt64)
    (h : stateGuard rho mx my energy = true) : StateBounds rho mx my energy := by
  rcases Bool.or_eq_true_iff.mp h with hn | he
  · exact Project.Euler2DConservative.Guard.stateGuard_spec rho mx my energy
      (Bool.or_eq_true_iff.mpr (Or.inl hn))
  · obtain ⟨hr, hm, ht, he, hrp, hep, hi⟩ :=
      Project.ProofKit.F64AdmissibilityTiny.checked_sound rho mx my energy he
    refine ⟨hr, hm, ht, he, hrp, hep, ?_⟩
    change 0 < CodeLib.IEEE64.value energy -
      ((CodeLib.IEEE64.value mx)^2 + (CodeLib.IEEE64.value my)^2) /
        (2 * CodeLib.IEEE64.value rho)
    apply sub_pos.mpr
    apply (div_lt_iff₀ (by positivity : 0 < 2 * CodeLib.IEEE64.value rho)).mpr
    nlinarith

theorem side_inputGuard (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    stateGuard rho mx my energy = true := by
  unfold sideCheckedBits at h
  split at h
  · assumption
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem side_outputPositive (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    positiveBits (sideCheckedBits rho mx my energy).pressure = true ∧
      positiveBits (sideCheckedBits rho mx my energy).speed = true := by
  generalize hr : sideCheckedBits rho mx my energy = out at h ⊢
  unfold sideCheckedBits at hr
  dsimp only at hr
  split_ifs at hr
  all_goals
    subst out
    first
    | exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    | simp only [Bool.and_eq_true_iff] at *
      exact ⟨by tauto, by tauto⟩

theorem side_state (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    Project.Euler2DCellStep.Safety.StateSafety rho mx my energy
      (sideCheckedBits rho mx my energy).pressure := by
  have hb := stateGuard_spec rho mx my energy (side_inputGuard rho mx my energy h)
  exact ⟨hb, ⟨hb.densityPositive,
    mul_pos (by norm_num : (0 : ℝ) < 2 / 5) hb.internalPositive⟩,
    (side_outputPositive rho mx my energy h).1⟩

theorem cell_state
    (ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR : UInt64)
    (h : (cellCheckedBits ratio rhoL mxL myL energyL rho mx my energy
      rhoR mxR myR energyR).status = 0) :
    let out := cellCheckedBits ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR
    Project.Euler2DCellStep.Safety.StateSafety out.density out.momentum out.transverse
      out.energy out.pressure := by
  generalize hr : cellCheckedBits ratio rhoL mxL myL energyL rho mx my energy
    rhoR mxR myR energyR = out at h ⊢
  unfold cellCheckedBits at hr
  dsimp only at hr
  split_ifs at hr
  all_goals
    subst out
    first
    | exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    | apply side_state
      simp only [beq_iff_eq] at *
      assumption

#print axioms stateGuard_extends
#print axioms side_eq_of_old_accepted
#print axioms stateGuard_spec
#print axioms side_state
#print axioms cell_state
end Project.EulerRiemann.Numerics
