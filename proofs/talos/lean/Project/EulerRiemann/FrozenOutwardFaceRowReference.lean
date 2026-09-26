import Project.EulerRiemann.FrozenOutwardFaceRowBalance
import Project.EulerRiemann.FrozenOutwardFluxResidual

namespace Project.EulerRiemann.Frozen.OutwardNumerics
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DConservative.Guard (decodedState)
open Numerics (stateWords fluxWords cellWords)
open scoped BigOperators

theorem accepted_face_row_flux (count : Nat) (hc : 0 < count) (ratio : UInt64)
    (state left right : Nat → State)
    (h : ∀ k < count, (faceRowStep ratio state left right k).status = 0)
    (k : Nat) (hk : k ≤ count) : (faceRowFlux left right k).status = 0 := by
  by_cases hlt : k < count
  · exact (advance_parts ratio (state k).density (state k).mx (state k).my (state k).energy
      (faceRowFlux left right k) (faceRowFlux left right (k + 1)) (h k hlt)).2.1
  · have he : k = count := by omega
    subst k
    have hb := (advance_parts ratio (state (count - 1)).density (state (count - 1)).mx
      (state (count - 1)).my (state (count - 1)).energy
      (faceRowFlux left right (count - 1)) (faceRowFlux left right (count - 1 + 1))
      (h (count - 1) (by omega))).2.2.1
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ count)] using hb

noncomputable def faceRowReference (left right : Nat → State) (k : Nat) (i : Fin 4) : ℝ :=
  RealRusanov.interfaceFlux (value (faceRowFlux left right k).alpha)
    (decodedState (left k).density (left k).mx (left k).my (left k).energy)
    (decodedState (right k).density (right k).mx (right k).my (right k).energy) i

noncomputable def faceRowFluxErrorBound (left right : Nat → State) (k : Nat) (i : Fin 4) : ℝ :=
  interfaceErrorBounds (left k).density (left k).mx (left k).my (left k).energy
    (right k).density (right k).mx (right k).my (right k).energy i

theorem accepted_face_row_flux_reference (count : Nat) (hc : 0 < count) (ratio : UInt64)
    (state left right : Nat → State)
    (h : ∀ k < count, (faceRowStep ratio state left right k).status = 0)
    (k : Nat) (hk : k ≤ count) (i : Fin 4) :
    |value (fluxWords (faceRowFlux left right k) i) - faceRowReference left right k i| ≤
      faceRowFluxErrorBound left right k i :=
  accepted_interface_reference_bound
    (left k).density (left k).mx (left k).my (left k).energy
    (right k).density (right k).mx (right k).my (right k).energy
    (accepted_face_row_flux count hc ratio state left right h k hk) i

noncomputable def faceRowReferenceResidual (count : Nat) (ratio : UInt64)
    (state left right : Nat → State) (i : Fin 4) : ℝ :=
  value ratio * ((value (fluxWords (faceRowFlux left right 0) i) - faceRowReference left right 0 i) -
    (value (fluxWords (faceRowFlux left right count) i) - faceRowReference left right count i)) +
    ∑ k ∈ Finset.range count, faceRowResidual ratio state left right k i

theorem accepted_face_row_reference_balance (count : Nat) (ratio : UInt64)
    (state left right : Nat → State)
    (h : ∀ k < count, (faceRowStep ratio state left right k).status = 0) (i : Fin 4) :
    (∑ k ∈ Finset.range count, value (cellWords (faceRowStep ratio state left right k) i)) -
      (∑ k ∈ Finset.range count,
        value (stateWords (state k).density (state k).mx (state k).my (state k).energy i)) =
      value ratio * (faceRowReference left right 0 i - faceRowReference left right count i) +
        faceRowReferenceResidual count ratio state left right i := by
  rw [accepted_face_row_balance count ratio state left right h i]
  unfold faceRowReferenceResidual
  ring

theorem accepted_face_row_reference_residual_bound (count : Nat) (hc : 0 < count) (ratio : UInt64)
    (state left right : Nat → State)
    (h : ∀ k < count, (faceRowStep ratio state left right k).status = 0) (i : Fin 4) :
    |faceRowReferenceResidual count ratio state left right i| ≤
      |value ratio| * (faceRowFluxErrorBound left right 0 i + faceRowFluxErrorBound left right count i) +
        ∑ k ∈ Finset.range count, faceRowErrorBound ratio state left right k i := by
  have hl := accepted_face_row_flux_reference count hc ratio state left right h 0 (Nat.zero_le _) i
  have hr := accepted_face_row_flux_reference count hc ratio state left right h count le_rfl i
  have hs := accepted_face_row_residual_bound count ratio state left right h i
  unfold faceRowReferenceResidual
  apply (abs_add_le _ _).trans
  apply add_le_add _ hs
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have ht := abs_sub_le
    (value (fluxWords (faceRowFlux left right 0) i) - faceRowReference left right 0 i) 0
    (value (fluxWords (faceRowFlux left right count) i) - faceRowReference left right count i)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  exact ht.trans (add_le_add hl hr)

#print axioms accepted_face_row_flux
#print axioms accepted_face_row_flux_reference
#print axioms accepted_face_row_reference_balance
#print axioms accepted_face_row_reference_residual_bound
end Project.EulerRiemann.Frozen.OutwardNumerics
