import Project.EulerRiemann.FrozenOutwardFaceStep
import Project.EulerRiemann.FrozenOutwardAdvanceResidual
import Project.ProofKit.RealFiniteVolumeBalance

namespace Project.EulerRiemann.Frozen.OutwardNumerics
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DCellStep.Model (CheckedCell)
open Project.Euler2DDynamicFlux.Model (CheckedFlux)
open Project.ProofKit.F64ConservativeUpdate
open Project.ProofKit.F64RoundingResidual (radius)
open Numerics (stateWords fluxWords cellWords)
open scoped BigOperators

def faceRowFlux (left right : Nat → State) (k : Nat) : CheckedFlux :=
  fluxCheckedBits (left k).density (left k).mx (left k).my (left k).energy
    (right k).density (right k).mx (right k).my (right k).energy

def faceRowStep (ratio : UInt64) (state left right : Nat → State) (k : Nat) : CheckedCell :=
  faceStepCheckedBits ratio (state k) (left k) (right k) (left (k + 1)) (right (k + 1))

noncomputable def faceRowResidual (ratio : UInt64)
    (state left right : Nat → State) (k : Nat) (i : Fin 4) : ℝ :=
  residual ratio
    (stateWords (state k).density (state k).mx (state k).my (state k).energy i)
    (fluxWords (faceRowFlux left right k) i)
    (fluxWords (faceRowFlux left right (k + 1)) i)
    (cellWords (faceRowStep ratio state left right k) i)

noncomputable def faceRowErrorBound (ratio : UInt64)
    (state left right : Nat → State) (k : Nat) (i : Fin 4) : ℝ :=
  let delta := Wasm.IEEE64.sub (fluxWords (faceRowFlux left right (k + 1)) i)
    (fluxWords (faceRowFlux left right k) i)
  |value ratio| * radius delta + radius (Wasm.IEEE64.mul ratio delta) +
    radius (cellWords (faceRowStep ratio state left right k) i)

theorem accepted_face_row_cell (ratio : UInt64) (state left right : Nat → State)
    (k : Nat) (h : (faceRowStep ratio state left right k).status = 0) (i : Fin 4) :
    value (cellWords (faceRowStep ratio state left right k) i) -
      value (stateWords (state k).density (state k).mx (state k).my (state k).energy i) =
      value ratio * (value (fluxWords (faceRowFlux left right k) i) -
        value (fluxWords (faceRowFlux left right (k + 1)) i)) +
        faceRowResidual ratio state left right k i ∧
    |faceRowResidual ratio state left right k i| ≤ faceRowErrorBound ratio state left right k i :=
  (advance_balance ratio (state k).density (state k).mx (state k).my (state k).energy
    (faceRowFlux left right k) (faceRowFlux left right (k + 1)) h i).2

theorem accepted_face_row_balance (count : Nat) (ratio : UInt64)
    (state left right : Nat → State)
    (h : ∀ k < count, (faceRowStep ratio state left right k).status = 0) (i : Fin 4) :
    (∑ k ∈ Finset.range count, value (cellWords (faceRowStep ratio state left right k) i)) -
      (∑ k ∈ Finset.range count,
        value (stateWords (state k).density (state k).mx (state k).my (state k).energy i)) =
      value ratio * (value (fluxWords (faceRowFlux left right 0) i) -
        value (fluxWords (faceRowFlux left right count) i)) +
        ∑ k ∈ Finset.range count, faceRowResidual ratio state left right k i := by
  rw [show value ratio * (value (fluxWords (faceRowFlux left right 0) i) -
      value (fluxWords (faceRowFlux left right count) i)) =
      -value ratio * (value (fluxWords (faceRowFlux left right count) i) -
        value (fluxWords (faceRowFlux left right 0) i)) by ring]
  apply Project.ProofKit.RealFiniteVolumeBalance.sweep_balance count (value ratio)
    (fun k => value (stateWords (state k).density (state k).mx (state k).my (state k).energy i))
    (fun k => value (cellWords (faceRowStep ratio state left right k) i))
    (fun k => value (fluxWords (faceRowFlux left right k) i))
    (fun k => faceRowResidual ratio state left right k i)
  intro k hk
  have hb := (accepted_face_row_cell ratio state left right k (h k hk) i).1
  linarith only [hb]

theorem accepted_face_row_residual_bound (count : Nat) (ratio : UInt64)
    (state left right : Nat → State)
    (h : ∀ k < count, (faceRowStep ratio state left right k).status = 0) (i : Fin 4) :
    |∑ k ∈ Finset.range count, faceRowResidual ratio state left right k i| ≤
      ∑ k ∈ Finset.range count, faceRowErrorBound ratio state left right k i := by
  calc
    _ ≤ ∑ k ∈ Finset.range count, |faceRowResidual ratio state left right k i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun k hk =>
      (accepted_face_row_cell ratio state left right k (h k (Finset.mem_range.mp hk)) i).2)

#print axioms accepted_face_row_cell
#print axioms accepted_face_row_balance
#print axioms accepted_face_row_residual_bound
end Project.EulerRiemann.Frozen.OutwardNumerics
