import Project.EulerRiemann.FrozenOutwardFaceStep
import Project.EulerRiemann.FrozenOutwardFluxSpec
import Project.EulerRiemann.FrozenOutwardAdvanceSpec
import Project.EulerRiemann.FrozenOutwardMeshSpec

namespace Project.EulerRiemann.Frozen.OutwardNumerics
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DCellStep.Model (rejectedCell)
open Project.Euler2DConservative.Guard (StateBounds decodedState)
open Project.Euler2DConservative.RealFlux (eigenvalues velocity soundSpeed)
open Project.ProofKit.F64Order (positiveBits_of_finite_value_pos positiveBits_spec)
open CodeLib.IEEE64

theorem face_step_bounds (ratio : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State)
    (h : (faceStepCheckedBits ratio center leftOuter leftInner rightInner rightOuter).status = 0) :
    let alpha := (faceStepCheckedBits ratio center leftOuter leftInner rightInner rightOuter).alpha
    OutwardMaximum.Bounds leftOuter alpha ∧ OutwardMaximum.Bounds leftInner alpha ∧
      OutwardMaximum.Bounds rightInner alpha ∧ OutwardMaximum.Bounds rightOuter alpha := by
  unfold faceStepCheckedBits at h ⊢
  generalize hlEq : fluxCheckedBits leftOuter.density leftOuter.mx leftOuter.my leftOuter.energy
    leftInner.density leftInner.mx leftInner.my leftInner.energy = left at h ⊢
  generalize hrEq : fluxCheckedBits rightInner.density rightInner.mx rightInner.my rightInner.energy
    rightOuter.density rightOuter.mx rightOuter.my rightOuter.energy = right at h ⊢
  have ha := advance_parts ratio center.density center.mx center.my center.energy left right h
  have hl := flux_bounds leftOuter.density leftOuter.mx leftOuter.my leftOuter.energy
    leftInner.density leftInner.mx leftInner.my leftInner.energy (by rw [hlEq]; exact ha.2.1)
  have hr := flux_bounds rightInner.density rightInner.mx rightInner.my rightInner.energy
    rightOuter.density rightOuter.mx rightOuter.my rightOuter.energy (by rw [hrEq]; exact ha.2.2.1)
  rw [hlEq] at hl
  rw [hrEq] at hr
  have hm := Project.EulerDynamicFlux.Safety.selected_speed_bound left.alpha right.alpha
    (positiveBits_of_finite_value_pos left.alpha hl.1 hl.2.1)
    (positiveBits_of_finite_value_pos right.alpha hr.1 hr.2.1)
  dsimp only
  rw [advance_alpha ratio center.density center.mx center.my center.energy left right h]
  exact ⟨OutwardMaximum.bounds_mono hl.2.2.1 hm.2.2.1,
    OutwardMaximum.bounds_mono hl.2.2.2 hm.2.2.1,
    OutwardMaximum.bounds_mono hr.2.2.1 hm.2.2.2,
    OutwardMaximum.bounds_mono hr.2.2.2 hm.2.2.2⟩

theorem face_step_characteristic_courant (ratio : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State)
    (h : (faceStepCheckedBits ratio center leftOuter leftInner rightInner rightOuter).status = 0)
    (face : State) (hf : face ∈ [leftOuter, leftInner, rightInner, rightOuter]) (i : Fin 4) :
    value ratio * |eigenvalues
      (velocity (decodedState face.density face.mx face.my face.energy))
      (soundSpeed (decodedState face.density face.mx face.my face.energy)) i| ≤ (1 : ℝ) / 2 := by
  have hc := advance_courant ratio center.density center.mx center.my center.energy _ _ h
  have hb := face_step_bounds ratio center leftOuter leftInner rightInner rightOuter h
  have hface : OutwardMaximum.Bounds face
      (faceStepCheckedBits ratio center leftOuter leftInner rightInner rightOuter).alpha := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact hb.1
    · exact hb.2.1
    · exact hb.2.2.1
    · exact hb.2.2.2
  exact (mul_le_mul_of_nonneg_left (hface.2 i)
    (positiveBits_spec ratio hc.1).2.le).trans (hc.2.2.2.2.1.trans hc.2.2.2.2.2)

theorem face_step_grid_characteristic_courant (n : Nat) (dt globalAlpha : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State)
    (hcfl : (OutwardCfl.gridRatioChecked n dt globalAlpha).status = 0)
    (h : (faceStepCheckedBits (OutwardCfl.gridRatioChecked n dt globalAlpha).value
      center leftOuter leftInner rightInner rightOuter).status = 0)
    (face : State) (hf : face ∈ [leftOuter, leftInner, rightInner, rightOuter]) (i : Fin 4) :
    value dt * (n : ℝ) * |eigenvalues
      (velocity (decodedState face.density face.mx face.my face.energy))
      (soundSpeed (decodedState face.density face.mx face.my face.energy)) i| ≤ (1 : ℝ) / 2 := by
  have hc := OutwardCfl.grid_ratio_accepted n dt globalAlpha hcfl
  exact (mul_le_mul_of_nonneg_right hc.2.2.2.2.2.1 (abs_nonneg _)).trans
    (face_step_characteristic_courant _ center leftOuter leftInner rightInner rightOuter h face hf i)

theorem face_step_behavior (ratio : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State) :
    let out := faceStepCheckedBits ratio center leftOuter leftInner rightInner rightOuter
    out = rejectedCell ∨ out.status = 0 ∧
      StateBounds out.density out.momentum out.transverse out.energy ∧
      Project.ProofKit.F64Order.positiveBits out.pressure = true ∧
      Project.ProofKit.F64Order.positiveBits ratio = true ∧
      Project.ProofKit.F64Order.positiveBits out.alpha = true ∧
      Finite out.courant ∧ 0 < value out.courant ∧
      value ratio * value out.alpha ≤ value out.courant ∧
      value out.courant ≤ (1 : ℝ) / 2 := by
  exact advance_behavior ratio center.density center.mx center.my center.energy _ _

#print axioms face_step_bounds
#print axioms face_step_characteristic_courant
#print axioms face_step_grid_characteristic_courant
#print axioms face_step_behavior
end Project.EulerRiemann.Frozen.OutwardNumerics
