import Project.EulerReconstructed.LineBalance
import Project.EulerRiemann.NumericsGridBalance

namespace Project.EulerReconstructed.Conservation
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep
open Project.EulerRiemann.Conservation (clamp normalComponent gridTotal gridTotal_as_lines)
open scoped BigOperators

noncomputable def gridComputedFlux {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, lineComputedFlux hn fuel axis grid (clamp hn k) (normalComponent axis i)

noncomputable def gridResidual {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (ratio : UInt64) (grid : Grid n n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, lineResidual hn fuel axis ratio grid (clamp hn k) (normalComponent axis i)

noncomputable def gridErrorBound {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (ratio : UInt64) (grid : Grid n n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, lineErrorBound hn fuel axis ratio grid (clamp hn k) (normalComponent axis i)

theorem accepted_grid_balance {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs fuel ratio axis grid)) (i : Fin 4) :
    gridTotal hn (nextGrid axis (Numerics.outputs fuel ratio axis grid)) i - gridTotal hn grid i =
      value ratio * gridComputedFlux hn fuel axis grid i + gridResidual hn fuel axis ratio grid i := by
  rw [gridTotal_as_lines hn axis, gridTotal_as_lines hn axis]
  unfold gridComputedFlux gridResidual
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ =>
    accepted_line_balance hn fuel axis ratio grid h (clamp hn k) (normalComponent axis i))

theorem accepted_grid_residual_bound {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (ratio : UInt64) (grid : Grid n n) (h : Accepted (Numerics.outputs fuel ratio axis grid)) (i : Fin 4) :
    |gridResidual hn fuel axis ratio grid i| ≤ gridErrorBound hn fuel axis ratio grid i := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ =>
    accepted_line_residual_bound hn fuel axis ratio grid h (clamp hn k) (normalComponent axis i)))

noncomputable def gridReferenceFlux {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, lineReferenceFlux hn fuel axis grid (clamp hn k) (normalComponent axis i)

noncomputable def gridFluxErrorBound {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, lineFluxErrorBound hn fuel axis grid (clamp hn k) (normalComponent axis i)

theorem grid_flux_reference_bound {n : Nat} (hn : 0 < n) (fuel : Nat) (axis : Bool)
    (ratio : UInt64) (grid : Grid n n) (h : Accepted (Numerics.outputs fuel ratio axis grid)) (i : Fin 4) :
    |gridComputedFlux hn fuel axis grid i - gridReferenceFlux hn fuel axis grid i| ≤
      gridFluxErrorBound hn fuel axis grid i := by
  unfold gridComputedFlux gridReferenceFlux gridFluxErrorBound
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ =>
    line_flux_reference_bound hn fuel axis ratio grid h (clamp hn k) (normalComponent axis i)))

#print axioms accepted_grid_balance
#print axioms accepted_grid_residual_bound
#print axioms grid_flux_reference_bound
end Project.EulerReconstructed.Conservation
