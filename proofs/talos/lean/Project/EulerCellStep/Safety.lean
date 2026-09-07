import Project.EulerCellStep.Model
import Project.EulerDynamicFlux.Safety

namespace Project.EulerCellStep.Safety
open Project.EulerConservative.Model (positiveBits finiteBits sideCheckedBits)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- The checked subtraction/multiplication/subtraction trace. -/
def updateWords (ratio state fluxL fluxR : UInt64) : List UInt64 :=
  let difference := Wasm.IEEE64.sub fluxR fluxL
  let increment := Wasm.IEEE64.mul ratio difference
  let value := Wasm.IEEE64.sub state increment
  [difference, increment, value]

private theorem finite_of_guard {word : UInt64} (h : finiteBits word = true) :
    CodeLib.IEEE64.Finite word := (Project.ProofKit.F64Order.finiteBits_iff word).mp h

theorem update_intermediates_finite (ratio state fluxL fluxR : UInt64)
    (h : (Model.updateCheckedBits ratio state fluxL fluxR).status = 0) :
    ∀ word ∈ updateWords ratio state fluxL fluxR, CodeLib.IEEE64.Finite word := by
  unfold Model.updateCheckedBits at h
  split at h
  · dsimp only at h
    split at h
    · rename_i hfinite
      obtain ⟨h2, hv⟩ := Bool.and_eq_true_iff.mp hfinite
      obtain ⟨hd, hi⟩ := Bool.and_eq_true_iff.mp h2
      simp only [updateWords, List.forall_mem_cons]
      exact ⟨finite_of_guard hd, finite_of_guard hi, finite_of_guard hv, List.forall_mem_nil _⟩
    · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

structure StateSafety (rho momentum energy pressure : UInt64) : Prop where
  bounds : Project.EulerConservative.Guard.StateBounds rho momentum energy
  admissible : Project.EulerRusanov.RealConservative.Admissible
    (Project.EulerConservative.Guard.decodedState rho momentum energy)
  pressurePositive : positiveBits pressure = true

private theorem stateSafety_of_side (rho momentum energy : UInt64)
    (h : (sideCheckedBits rho momentum energy).status = 0) :
    StateSafety rho momentum energy (sideCheckedBits rho momentum energy).pressure := by
  exact ⟨Project.EulerConservative.Guard.stateGuard_spec _ _ _
      (Project.EulerConservative.Safety.accepted_inputGuard _ _ _ h),
    Project.EulerConservative.Safety.accepted_admissible _ _ _ h,
    (Project.EulerConservative.Safety.accepted_outputPositive _ _ _ h).1⟩

theorem accepted_state (ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR : UInt64)
    (h : (Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR).status = 0) :
    let out := Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR
    StateSafety out.density out.momentum out.energy out.pressure := by
  generalize hresult : Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR = result at h ⊢
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

theorem accepted_courant_guard (ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR : UInt64)
    (h : (Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR).status = 0) :
    let courant := (Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR).courant
    positiveBits courant = true ∧ courant ≤ 0x3FE0000000000000 := by
  generalize hresult : Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR = result at h ⊢
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
theorem accepted_courant (ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR : UInt64)
    (h : (Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR).status = 0) :
    let courant := (Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR).courant
    CodeLib.IEEE64.Finite courant ∧ 0 < CodeLib.IEEE64.value courant ∧ CodeLib.IEEE64.value courant ≤ (1 : ℝ) / 2 := by
  obtain ⟨hpositive, hle⟩ := accepted_courant_guard _ _ _ _ _ _ _ _ _ _ h
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
theorem accepted_alpha (ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR : UInt64)
    (h : (Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR).status = 0) :
    positiveBits (Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR).alpha = true := by
  generalize hresult : Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR = result at h ⊢
  unfold Model.cellCheckedBits at hresult
  dsimp only at hresult
  split_ifs at hresult
  all_goals
    subst result
    first
    | exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    | simp only [beq_iff_eq] at *
      first
      | exact (Project.EulerDynamicFlux.Safety.accepted_fields rho momentum energy rhoR momentumR energyR (by assumption)).2.2.2
      | exact (Project.EulerDynamicFlux.Safety.accepted_fields rhoL momentumL energyL rho momentum energy (by assumption)).2.2.2

#print axioms accepted_alpha
#print axioms accepted_courant
#print axioms update_intermediates_finite
#print axioms accepted_state
#print axioms accepted_courant_guard
end Project.EulerCellStep.Safety
