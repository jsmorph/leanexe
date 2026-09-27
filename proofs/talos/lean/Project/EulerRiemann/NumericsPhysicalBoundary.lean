import Project.EulerRiemann.NumericsBoundaryFlux
import Project.EulerRiemann.NumericsRatioResidual

namespace Project.EulerRiemann.Conservation
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep
open Numerics (rowCellFlux fluxWords)
open scoped BigOperators

noncomputable def lineComputedFlux {n : Nat} (hn : 0 < n) (axis : Bool)
    (grid : Grid n n) (line : Fin n) (i : Fin 4) : ℝ :=
  value (fluxWords (rowCellFlux (lineState hn axis grid line) 0) i) -
    value (fluxWords (rowCellFlux (lineState hn axis grid line) n) i)

noncomputable def linePhysicalFlux {n : Nat} (hn : 0 < n) (axis : Bool)
    (grid : Grid n n) (line : Fin n) (i : Fin 4) : ℝ :=
  physicalStateFlux (lineState hn axis grid line 0) i -
    physicalStateFlux (lineState hn axis grid line (n - 1)) i

noncomputable def lineFluxErrorBound {n : Nat} (hn : 0 < n) (axis : Bool)
    (grid : Grid n n) (line : Fin n) (i : Fin 4) : ℝ :=
  constantFluxErrorBound (lineState hn axis grid line 0) i +
    constantFluxErrorBound (lineState hn axis grid line (n - 1)) i

theorem line_flux_reference_bound {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs ratio axis grid)) (line : Fin n) (i : Fin 4) :
    |lineComputedFlux hn axis grid line i - linePhysicalFlux hn axis grid line i| ≤
      lineFluxErrorBound hn axis grid line i := by
  obtain ⟨hl, hr⟩ := line_boundary_accepted hn axis ratio grid h line
  have bl := constant_flux_reference_bound _ hl i
  have br := constant_flux_reference_bound _ hr i
  unfold lineComputedFlux linePhysicalFlux lineFluxErrorBound
  rw [line_left_flux, line_right_flux]
  calc
    _ = |(value (fluxWords (constantFlux (lineState hn axis grid line 0)) i) -
        physicalStateFlux (lineState hn axis grid line 0) i) +
      -(value (fluxWords (constantFlux (lineState hn axis grid line (n - 1))) i) -
        physicalStateFlux (lineState hn axis grid line (n - 1)) i)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (by simpa only [abs_neg] using add_le_add bl br)

noncomputable def gridComputedFlux {n : Nat} (hn : 0 < n) (axis : Bool)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, lineComputedFlux hn axis grid (clamp hn k) (normalComponent axis i)

noncomputable def gridPhysicalFlux {n : Nat} (hn : 0 < n) (axis : Bool)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, linePhysicalFlux hn axis grid (clamp hn k) (normalComponent axis i)

noncomputable def gridFluxErrorBound {n : Nat} (hn : 0 < n) (axis : Bool)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, lineFluxErrorBound hn axis grid (clamp hn k) (normalComponent axis i)

theorem grid_flux_reference_bound {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs ratio axis grid)) (i : Fin 4) :
    |gridComputedFlux hn axis grid i - gridPhysicalFlux hn axis grid i| ≤
      gridFluxErrorBound hn axis grid i := by
  unfold gridComputedFlux gridPhysicalFlux gridFluxErrorBound
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ =>
    line_flux_reference_bound hn axis ratio grid h (clamp hn k) (normalComponent axis i)))

theorem gridBoundary_as_flux {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (i : Fin 4) :
    gridBoundary hn axis ratio grid i = value ratio * gridComputedFlux hn axis grid i := by
  unfold gridBoundary gridComputedFlux
  rw [Finset.mul_sum]
  rfl

noncomputable def gridPhysicalResidual {n : Nat} (hn : 0 < n) (axis : Bool) (ratio dt : UInt64)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  gridBoundary hn axis ratio grid i - value dt * (n : ℝ) * gridPhysicalFlux hn axis grid i

noncomputable def gridPhysicalErrorBound {n : Nat} (hn : 0 < n) (axis : Bool) (ratio dt : UInt64)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  |value ratio| * gridFluxErrorBound hn axis grid i +
    ratioErrorBound n dt * |gridPhysicalFlux hn axis grid i|

theorem grid_physical_residual_bound {n : Nat} (hn : 0 < n) (axis : Bool) (ratio dt : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs ratio axis grid))
    (hr : |value ratio - value dt * (n : ℝ)| ≤ ratioErrorBound n dt) (i : Fin 4) :
    |gridPhysicalResidual hn axis ratio dt grid i| ≤ gridPhysicalErrorBound hn axis ratio dt grid i := by
  unfold gridPhysicalResidual gridPhysicalErrorBound
  rw [gridBoundary_as_flux]
  exact Project.ProofKit.RealProductError.product_error _ _ _ _ _ _ _ _ hr
    (grid_flux_reference_bound hn axis ratio grid h i) le_rfl le_rfl

#print axioms line_flux_reference_bound
#print axioms grid_flux_reference_bound
#print axioms grid_physical_residual_bound
end Project.EulerRiemann.Conservation
