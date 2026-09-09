import Project.Euler2DCellStep.Model
import Project.Euler2DDynamicFlux.Safety

namespace Project.Euler2DCellStep.Safety
open Project.Euler2DConservative.Model (positiveBits finiteBits sideCheckedBits)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

structure StateSafety (rho momentum transverse energy pressure : UInt64) : Prop where
  bounds : Project.Euler2DConservative.Guard.StateBounds rho momentum transverse energy
  admissible : Project.Euler2DConservative.Guard.Admissible
    (Project.Euler2DConservative.Guard.decodedState rho momentum transverse energy)
  pressurePositive : positiveBits pressure = true

private theorem stateSafety_of_side (rho momentum transverse energy : UInt64)
    (h : (sideCheckedBits rho momentum transverse energy).status = 0) :
    StateSafety rho momentum transverse energy (sideCheckedBits rho momentum transverse energy).pressure := by
  exact ⟨Project.Euler2DConservative.Guard.stateGuard_spec _ _ _ _
      (Project.Euler2DConservative.Safety.accepted_inputGuard _ _ _ _ h),
    Project.Euler2DConservative.Safety.accepted_admissible _ _ _ _ h,
    (Project.Euler2DConservative.Safety.accepted_outputPositive _ _ _ _ h).1⟩

theorem accepted_state (ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR : UInt64)
    (h : (Model.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR).status = 0) :
    let out := Model.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR
    StateSafety out.density out.momentum out.transverse out.energy out.pressure := by
  generalize hresult : Model.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR = result at h ⊢
  unfold Model.cellCheckedBits at hresult
  dsimp only at hresult
  split_ifs at hresult
  all_goals
    subst result
    first
    | exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    | apply stateSafety_of_side
      simp only [beq_iff_eq] at *
      assumption

theorem accepted_courant_guard (ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR : UInt64)
    (h : (Model.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR).status = 0) :
    let courant := (Model.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR).courant
    positiveBits courant = true ∧ courant ≤ 0x3FE0000000000000 := by
  generalize hresult : Model.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR = result at h ⊢
  unfold Model.cellCheckedBits at hresult
  dsimp only at hresult
  split_ifs at hresult
  all_goals
    subst result
    first
    | exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    | simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at *
      assumption

private theorem half_value : CodeLib.IEEE64.value (0x3FE0000000000000 : UInt64) = (1 : ℝ) / 2 := by
  have hbits : (0x3FE0000000000000 : UInt64) = Wasm.IEEE64.encodeFinite false 1022 0 := by
    norm_num [Wasm.IEEE64.encodeFinite]
    rfl
  rw [hbits, CodeLib.IEEE64.value,
    CodeLib.IEEE64.scaledValue_encodeFinite false 1022 0 (by norm_num) (by norm_num)]
  norm_num [pow_succ]

/-- The checked rounded Courant number decodes to a real number in (0, 1/2]. -/
theorem accepted_courant (ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR : UInt64)
    (h : (Model.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR).status = 0) :
    let courant := (Model.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR).courant
    CodeLib.IEEE64.Finite courant ∧ 0 < CodeLib.IEEE64.value courant ∧ CodeLib.IEEE64.value courant ≤ (1 : ℝ) / 2 := by
  obtain ⟨hpositive, hle⟩ := accepted_courant_guard _ _ _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨hfinite, hvalue⟩ := Project.ProofKit.F64Order.positiveBits_spec _ hpositive
  have hhalf : positiveBits (0x3FE0000000000000 : UInt64) = true := by decide
  have horder := Project.ProofKit.F64Order.abs_value_mono _ _ (show
      Project.ProofKit.F64Order.absBits _ ≤ Project.ProofKit.F64Order.absBits (0x3FE0000000000000 : UInt64) by
    rw [Project.ProofKit.F64Order.absBits_of_positive _ hpositive,
      Project.ProofKit.F64Order.absBits_of_positive _ hhalf]
    exact hle)
  rw [abs_of_pos hvalue, half_value, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at horder
  exact ⟨hfinite, hvalue, horder⟩

/-- The selected diagnostic speed is finite and strictly positive on acceptance. -/
theorem accepted_alpha (ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR : UInt64)
    (h : (Model.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR).status = 0) :
    positiveBits (Model.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR).alpha = true := by
  generalize hresult : Model.cellCheckedBits ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR = result at h ⊢
  unfold Model.cellCheckedBits at hresult
  dsimp only at hresult
  split_ifs at hresult
  all_goals
    subst result
    first
    | exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    | simp only [beq_iff_eq] at *
      first
      | exact (Project.Euler2DDynamicFlux.Safety.accepted_fields rho momentum transverse energy rhoR momentumR transverseR energyR (by assumption)).2.2.2.2
      | exact (Project.Euler2DDynamicFlux.Safety.accepted_fields rhoL momentumL transverseL energyL rho momentum transverse energy (by assumption)).2.2.2.2

#print axioms accepted_alpha
#print axioms accepted_courant
#print axioms accepted_state
#print axioms accepted_courant_guard
end Project.Euler2DCellStep.Safety
