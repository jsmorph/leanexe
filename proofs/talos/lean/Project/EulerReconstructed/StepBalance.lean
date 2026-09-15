import Project.EulerReconstructed.GridBalance
import Project.EulerReconstructed.TraversalModel

namespace Project.EulerReconstructed.Conservation
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep
open Project.EulerRiemann.Conservation (gridTotal)
open Project.EulerRiemann.Traversal (Cell Indexed accepted asGrid)

theorem accepted_step_parts (n fuel : Nat) (ratio : UInt64) (grid : Array Cell)
    (ha : accepted (Traversal.step n fuel ratio grid) = true) :
    accepted (Traversal.sweep n fuel false ratio grid) = true ∧
    accepted (Traversal.sweep n fuel true ratio (Traversal.sweep n fuel false ratio grid)) = true ∧
    Traversal.step n fuel ratio grid =
      Traversal.sweep n fuel true ratio (Traversal.sweep n fuel false ratio grid) := by
  unfold Traversal.step at ha ⊢
  dsimp only at ha ⊢
  split_ifs at ha ⊢ with hx
  · exact ⟨hx, ha, rfl⟩
  · contradiction

noncomputable def stepComputedFlux {n : Nat} (hn : 0 < n) (fuel : Nat) (ratio : UInt64)
    (grid : Array Cell) (i : Fin 4) : ℝ :=
  gridComputedFlux hn fuel false (asGrid n grid) i +
    gridComputedFlux hn fuel true (asGrid n (Traversal.sweep n fuel false ratio grid)) i

noncomputable def stepBoundary {n : Nat} (hn : 0 < n) (fuel : Nat) (ratio : UInt64)
    (grid : Array Cell) (i : Fin 4) : ℝ := value ratio * stepComputedFlux hn fuel ratio grid i

noncomputable def stepResidual {n : Nat} (hn : 0 < n) (fuel : Nat) (ratio : UInt64)
    (grid : Array Cell) (i : Fin 4) : ℝ :=
  gridResidual hn fuel false ratio (asGrid n grid) i +
    gridResidual hn fuel true ratio (asGrid n (Traversal.sweep n fuel false ratio grid)) i

noncomputable def stepErrorBound {n : Nat} (hn : 0 < n) (fuel : Nat) (ratio : UInt64)
    (grid : Array Cell) (i : Fin 4) : ℝ :=
  gridErrorBound hn fuel false ratio (asGrid n grid) i +
    gridErrorBound hn fuel true ratio (asGrid n (Traversal.sweep n fuel false ratio grid)) i

theorem accepted_step_balance {n : Nat} (hn : 0 < n) (fuel : Nat) (ratio : UInt64)
    (grid : Array Cell) (hg : Indexed n grid)
    (ha : accepted (Traversal.step n fuel ratio grid) = true) (i : Fin 4) :
    gridTotal hn (asGrid n (Traversal.step n fuel ratio grid)) i - gridTotal hn (asGrid n grid) i =
      stepBoundary hn fuel ratio grid i + stepResidual hn fuel ratio grid i := by
  obtain ⟨hx, hy, he⟩ := accepted_step_parts n fuel ratio grid ha
  have hm := Traversal.sweep_indexed n fuel false ratio grid hg
  have bx := accepted_grid_balance hn fuel false ratio (asGrid n grid)
    ((Traversal.sweep_accepted_iff n fuel false ratio grid hg).mp hx) i
  have by' := accepted_grid_balance hn fuel true ratio (asGrid n (Traversal.sweep n fuel false ratio grid))
    ((Traversal.sweep_accepted_iff n fuel true ratio _ hm).mp hy) i
  rw [← Traversal.sweep_asGrid n fuel false ratio grid hg] at bx
  rw [← Traversal.sweep_asGrid n fuel true ratio _ hm, ← he] at by'
  unfold stepBoundary stepComputedFlux stepResidual
  linarith only [bx, by']

theorem accepted_step_residual_bound {n : Nat} (hn : 0 < n) (fuel : Nat) (ratio : UInt64)
    (grid : Array Cell) (hg : Indexed n grid)
    (ha : accepted (Traversal.step n fuel ratio grid) = true) (i : Fin 4) :
    |stepResidual hn fuel ratio grid i| ≤ stepErrorBound hn fuel ratio grid i := by
  obtain ⟨hx, hy, _⟩ := accepted_step_parts n fuel ratio grid ha
  have hm := Traversal.sweep_indexed n fuel false ratio grid hg
  exact (abs_add_le _ _).trans (add_le_add
    (accepted_grid_residual_bound hn fuel false ratio (asGrid n grid)
      ((Traversal.sweep_accepted_iff n fuel false ratio grid hg).mp hx) i)
    (accepted_grid_residual_bound hn fuel true ratio (asGrid n (Traversal.sweep n fuel false ratio grid))
      ((Traversal.sweep_accepted_iff n fuel true ratio _ hm).mp hy) i))

#print axioms accepted_step_parts
#print axioms accepted_step_balance
#print axioms accepted_step_residual_bound
end Project.EulerReconstructed.Conservation
