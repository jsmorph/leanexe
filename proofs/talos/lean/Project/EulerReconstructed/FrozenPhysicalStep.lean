import Project.EulerReconstructed.FrozenTraceBalance
import Project.EulerReconstructed.FrozenRatioResidual
import Project.ProofKit.RealProductError

namespace Project.EulerReconstructed.Frozen.Conservation
open CodeLib.IEEE64
open Project.EulerRiemann.Frozen.Traversal (Cell Indexed accepted asGrid)
open Project.EulerRiemann.Frozen.Conservation (gridTotal)

noncomputable def stepReferenceFlux {n : Nat} (hn : 0 < n) (fuel : Nat) (ratio : UInt64)
    (grid : Array Cell) (i : Fin 4) : ℝ :=
  gridReferenceFlux hn fuel false (asGrid n grid) i +
    gridReferenceFlux hn fuel true (asGrid n (Traversal.sweep n fuel false ratio grid)) i

noncomputable def stepFluxErrorBound {n : Nat} (hn : 0 < n) (fuel : Nat) (ratio : UInt64)
    (grid : Array Cell) (i : Fin 4) : ℝ :=
  gridFluxErrorBound hn fuel false (asGrid n grid) i +
    gridFluxErrorBound hn fuel true (asGrid n (Traversal.sweep n fuel false ratio grid)) i

theorem step_flux_reference_bound {n : Nat} (hn : 0 < n) (fuel : Nat) (ratio : UInt64)
    (grid : Array Cell) (hg : Indexed n grid)
    (ha : accepted (Traversal.step n fuel ratio grid) = true) (i : Fin 4) :
    |stepComputedFlux hn fuel ratio grid i - stepReferenceFlux hn fuel ratio grid i| ≤
      stepFluxErrorBound hn fuel ratio grid i := by
  obtain ⟨hx, hy, _⟩ := accepted_step_parts n fuel ratio grid ha
  have hm := Traversal.sweep_indexed n fuel false ratio grid hg
  have bx := grid_flux_reference_bound hn fuel false ratio (asGrid n grid)
    ((Traversal.sweep_accepted_iff n fuel false ratio grid hg).mp hx) i
  have by' := grid_flux_reference_bound hn fuel true ratio (asGrid n (Traversal.sweep n fuel false ratio grid))
    ((Traversal.sweep_accepted_iff n fuel true ratio _ hm).mp hy) i
  unfold stepComputedFlux stepReferenceFlux stepFluxErrorBound
  rw [show ∀ a b c d : ℝ, a + b - (c + d) = (a - c) + (b - d) by intros; ring]
  exact (abs_add_le _ _).trans (add_le_add bx by')

noncomputable def physicalTotal {n : Nat} (hn : 0 < n) (grid : Array Cell) (i : Fin 4) : ℝ :=
  gridTotal hn (asGrid n grid) i / (n : ℝ) ^ 2

noncomputable def stepPhysicalBoundary {n : Nat} (hn : 0 < n) (fuel : Nat) (dt : UInt64)
    (grid : Array Cell) (i : Fin 4) : ℝ :=
  value dt / (n : ℝ) * stepReferenceFlux hn fuel (traceRatio n dt grid) grid i

noncomputable def stepPhysicalResidual {n : Nat} (hn : 0 < n) (fuel : Nat) (dt : UInt64)
    (grid : Array Cell) (i : Fin 4) : ℝ :=
  let ratio := traceRatio n dt grid
  (stepResidual hn fuel ratio grid i +
    (value ratio * stepComputedFlux hn fuel ratio grid i -
      value dt * (n : ℝ) * stepReferenceFlux hn fuel ratio grid i)) / (n : ℝ) ^ 2

noncomputable def stepPhysicalErrorBound {n : Nat} (hn : 0 < n) (fuel : Nat) (dt : UInt64)
    (grid : Array Cell) (i : Fin 4) : ℝ :=
  let ratio := traceRatio n dt grid
  (stepErrorBound hn fuel ratio grid i +
    (|value ratio| * stepFluxErrorBound hn fuel ratio grid i +
      ratioErrorBound n dt * |stepReferenceFlux hn fuel ratio grid i|)) / (n : ℝ) ^ 2

theorem step_physical_balance {n : Nat} (hn : 0 < n) (fuel : Nat) (dt : UInt64)
    (grid : Array Cell) (hg : Indexed n grid)
    (ha : accepted (Traversal.step n fuel (traceRatio n dt grid) grid) = true) (i : Fin 4) :
    physicalTotal hn (Traversal.step n fuel (traceRatio n dt grid) grid) i - physicalTotal hn grid i =
      stepPhysicalBoundary hn fuel dt grid i + stepPhysicalResidual hn fuel dt grid i := by
  have hb := accepted_step_balance hn fuel (traceRatio n dt grid) grid hg ha i
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold physicalTotal stepPhysicalBoundary stepPhysicalResidual
  dsimp only
  rw [← sub_div, hb]
  unfold stepBoundary
  field_simp [hnR]
  ring

theorem step_physical_residual_bound {n : Nat} (hn : 0 < n) (fuel : Nat) (dt : UInt64)
    (grid : Array Cell) (hg : Indexed n grid)
    (hr : (Project.EulerRiemann.Frozen.OutwardCfl.gridRatioChecked n dt
      (Project.EulerRiemann.Frozen.OutwardMaximum.gridUpper grid).value).status = 0)
    (ha : accepted (Traversal.step n fuel (traceRatio n dt grid) grid) = true) (i : Fin 4) :
    |stepPhysicalResidual hn fuel dt grid i| ≤ stepPhysicalErrorBound hn fuel dt grid i := by
  have bu := accepted_step_residual_bound hn fuel (traceRatio n dt grid) grid hg ha i
  have bf := step_flux_reference_bound hn fuel (traceRatio n dt grid) grid hg ha i
  have br := ratio_error n dt _ hr
  have bp := Project.ProofKit.RealProductError.product_error _ _ _ _ _ _ _ _ br bf le_rfl le_rfl
  unfold stepPhysicalResidual stepPhysicalErrorBound
  dsimp only
  rw [abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
  exact div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add bu bp)) (sq_nonneg (n : ℝ))

#print axioms step_flux_reference_bound
#print axioms step_physical_balance
#print axioms step_physical_residual_bound
end Project.EulerReconstructed.Frozen.Conservation
