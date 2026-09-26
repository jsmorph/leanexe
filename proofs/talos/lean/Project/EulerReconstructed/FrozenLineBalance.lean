import Project.EulerReconstructed.FrozenLineGeometry
import Project.EulerRiemann.FrozenNumericsLineBalance
import Project.EulerRiemann.FrozenOutwardFaceRowReference

namespace Project.EulerReconstructed.Frozen.Conservation
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep
open Project.EulerRiemann.Frozen.Conservation (lineState lineTotal stateValue)
open Project.EulerRiemann.Frozen.Numerics (fluxWords cellWords)
open Project.EulerRiemann.Frozen.OutwardNumerics
open Numerics (rowCenter rowLeft rowRight)
open scoped BigOperators

def lineLeft {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (grid : Grid n n) (line : Fin n) : Nat → State := rowLeft fuel (paddedState hn axis grid line)

def lineRight {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (grid : Grid n n) (line : Fin n) : Nat → State := rowRight fuel (paddedState hn axis grid line)

noncomputable def lineComputedFlux {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (grid : Grid n n) (line : Fin n) (i : Fin 4) : ℝ :=
  value (fluxWords (faceRowFlux (lineLeft hn fuel axis grid line) (lineRight hn fuel axis grid line) 0) i) -
    value (fluxWords (faceRowFlux (lineLeft hn fuel axis grid line) (lineRight hn fuel axis grid line) n) i)

noncomputable def lineResidual {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (ratio : UInt64) (grid : Grid n n) (line : Fin n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, faceRowResidual ratio (rowCenter (paddedState hn axis grid line))
    (lineLeft hn fuel axis grid line) (lineRight hn fuel axis grid line) k i

noncomputable def lineErrorBound {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (ratio : UInt64) (grid : Grid n n) (line : Fin n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, faceRowErrorBound ratio (rowCenter (paddedState hn axis grid line))
    (lineLeft hn fuel axis grid line) (lineRight hn fuel axis grid line) k i

theorem line_total_delta {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs fuel ratio axis grid))
    (line : Fin n) (i : Fin 4) :
    lineTotal hn axis (nextGrid axis (Numerics.outputs fuel ratio axis grid)) line i -
      lineTotal hn axis grid line i =
    (∑ k ∈ Finset.range n, value (cellWords (faceRowStep ratio
      (rowCenter (paddedState hn axis grid line)) (lineLeft hn fuel axis grid line)
      (lineRight hn fuel axis grid line) k) i)) -
    (∑ k ∈ Finset.range n, stateValue (rowCenter (paddedState hn axis grid line) k) i) := by
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have ha := line_accepted hn fuel axis ratio grid h line k (Finset.mem_range.mp hk)
    unfold stateValue
    rw [line_next_words hn fuel axis ratio grid line k (Finset.mem_range.mp hk) i]
    rw [Numerics.accepted_row_evaluate fuel ratio _ k ha]
    rfl

theorem accepted_line_balance {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs fuel ratio axis grid))
    (line : Fin n) (i : Fin 4) :
    lineTotal hn axis (nextGrid axis (Numerics.outputs fuel ratio axis grid)) line i -
      lineTotal hn axis grid line i = value ratio * lineComputedFlux hn fuel axis grid line i +
        lineResidual hn fuel axis ratio grid line i := by
  rw [line_total_delta hn fuel axis ratio grid h line i]
  exact accepted_face_row_balance n ratio _ _ _ (line_face_accepted hn fuel axis ratio grid h line) i

theorem accepted_line_residual_bound {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (ratio : UInt64) (grid : Grid n n) (h : Accepted (Numerics.outputs fuel ratio axis grid))
    (line : Fin n) (i : Fin 4) :
    |lineResidual hn fuel axis ratio grid line i| ≤ lineErrorBound hn fuel axis ratio grid line i :=
  accepted_face_row_residual_bound n ratio _ _ _ (line_face_accepted hn fuel axis ratio grid h line) i

noncomputable def lineReferenceFlux {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (grid : Grid n n) (line : Fin n) (i : Fin 4) : ℝ :=
  faceRowReference (lineLeft hn fuel axis grid line) (lineRight hn fuel axis grid line) 0 i -
    faceRowReference (lineLeft hn fuel axis grid line) (lineRight hn fuel axis grid line) n i

noncomputable def lineFluxErrorBound {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (grid : Grid n n) (line : Fin n) (i : Fin 4) : ℝ :=
  faceRowFluxErrorBound (lineLeft hn fuel axis grid line) (lineRight hn fuel axis grid line) 0 i +
    faceRowFluxErrorBound (lineLeft hn fuel axis grid line) (lineRight hn fuel axis grid line) n i

theorem line_flux_reference_bound {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (ratio : UInt64) (grid : Grid n n) (h : Accepted (Numerics.outputs fuel ratio axis grid))
    (line : Fin n) (i : Fin 4) :
    |lineComputedFlux hn fuel axis grid line i - lineReferenceFlux hn fuel axis grid line i| ≤
      lineFluxErrorBound hn fuel axis grid line i := by
  have hl := accepted_face_row_flux_reference n hn ratio _ _ _
    (line_face_accepted hn fuel axis ratio grid h line) 0 (Nat.zero_le _) i
  have hr := accepted_face_row_flux_reference n hn ratio _ _ _
    (line_face_accepted hn fuel axis ratio grid h line) n le_rfl i
  unfold lineComputedFlux lineReferenceFlux lineFluxErrorBound
  calc
    _ = |(value (fluxWords (faceRowFlux (lineLeft hn fuel axis grid line)
          (lineRight hn fuel axis grid line) 0) i) -
        faceRowReference (lineLeft hn fuel axis grid line) (lineRight hn fuel axis grid line) 0 i) -
      (value (fluxWords (faceRowFlux (lineLeft hn fuel axis grid line)
          (lineRight hn fuel axis grid line) n) i) -
        faceRowReference (lineLeft hn fuel axis grid line) (lineRight hn fuel axis grid line) n i)| := by
      congr 1
      ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add hl hr)

#print axioms line_total_delta
#print axioms accepted_line_balance
#print axioms accepted_line_residual_bound
#print axioms line_flux_reference_bound
end Project.EulerReconstructed.Frozen.Conservation
