import Project.EulerRiemann.OutwardFaceStep
import Project.EulerRiemann.OutwardAdvanceResidual
import Project.EulerRiemann.OutwardFluxResidual
import Project.ProofKit.F64ConservativeReference

namespace Project.EulerRiemann.OutwardNumerics
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DConservative.Guard (decodedState)
open Project.ProofKit.F64ConservativeUpdate
open Project.ProofKit.F64RoundingResidual (radius)
open Numerics (stateWords fluxWords cellWords)

theorem face_step_reference_bound (ratio : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State)
    (h : (faceStepCheckedBits ratio center leftOuter leftInner rightInner rightOuter).status = 0)
    (i : Fin 4) :
    let left := fluxCheckedBits leftOuter.density leftOuter.mx leftOuter.my leftOuter.energy
      leftInner.density leftInner.mx leftInner.my leftInner.energy
    let right := fluxCheckedBits rightInner.density rightInner.mx rightInner.my rightInner.energy
      rightOuter.density rightOuter.mx rightOuter.my rightOuter.energy
    let refL := RealRusanov.interfaceFlux (value left.alpha)
      (decodedState leftOuter.density leftOuter.mx leftOuter.my leftOuter.energy)
      (decodedState leftInner.density leftInner.mx leftInner.my leftInner.energy) i
    let refR := RealRusanov.interfaceFlux (value right.alpha)
      (decodedState rightInner.density rightInner.mx rightInner.my rightInner.energy)
      (decodedState rightOuter.density rightOuter.mx rightOuter.my rightOuter.energy) i
    let state := stateWords center.density center.mx center.my center.energy i
    let fl := fluxWords left i
    let fr := fluxWords right i
    let out := cellWords (faceStepCheckedBits ratio center leftOuter leftInner rightInner rightOuter) i
    Certificate ratio state fl fr out ∧
      |value out - (value state - value ratio * (refR - refL))| ≤
        |value ratio| * radius (Wasm.IEEE64.sub fr fl) +
        radius (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fr fl)) + radius out +
        |value ratio| * (interfaceErrorBounds
          leftOuter.density leftOuter.mx leftOuter.my leftOuter.energy
          leftInner.density leftInner.mx leftInner.my leftInner.energy i +
          interfaceErrorBounds
          rightInner.density rightInner.mx rightInner.my rightInner.energy
          rightOuter.density rightOuter.mx rightOuter.my rightOuter.energy i) := by
  unfold faceStepCheckedBits at h ⊢
  generalize hlEq : fluxCheckedBits leftOuter.density leftOuter.mx leftOuter.my leftOuter.energy
    leftInner.density leftInner.mx leftInner.my leftInner.energy = left at h ⊢
  generalize hrEq : fluxCheckedBits rightInner.density rightInner.mx rightInner.my rightInner.energy
    rightOuter.density rightOuter.mx rightOuter.my rightOuter.energy = right at h ⊢
  have ha := advance_parts ratio center.density center.mx center.my center.energy left right h
  have hu := (advance_balance ratio center.density center.mx center.my center.energy left right h i).1
  have hl := accepted_interface_reference_bound
    leftOuter.density leftOuter.mx leftOuter.my leftOuter.energy
    leftInner.density leftInner.mx leftInner.my leftInner.energy
    (by rw [hlEq]; exact ha.2.1) i
  have hr := accepted_interface_reference_bound
    rightInner.density rightInner.mx rightInner.my rightInner.energy
    rightOuter.density rightOuter.mx rightOuter.my rightOuter.energy
    (by rw [hrEq]; exact ha.2.2.1) i
  rw [hlEq] at hl
  rw [hrEq] at hr
  exact ⟨hu, reference_bound hu _ _ _ _ hl hr⟩

#print axioms face_step_reference_bound
end Project.EulerRiemann.OutwardNumerics
