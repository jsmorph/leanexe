import Project.EulerRiemann.FrozenNumericsGridBalance

namespace Project.EulerRiemann.Frozen.Conservation
open Project.Euler2DCellStep.Sweep

def middleGrid {n : Nat} (ratio : UInt64) (grid : Grid n n) : Grid n n :=
  nextGrid false (Numerics.outputs ratio false grid)

def stepGrid {n : Nat} (ratio : UInt64) (grid : Grid n n) : Grid n n :=
  nextGrid true (Numerics.outputs ratio true (middleGrid ratio grid))

theorem accepted_step_parts {n : Nat} (ratio : UInt64) (grid next : Grid n n)
    (h : Numerics.step ratio grid = some next) :
    Accepted (Numerics.outputs ratio false grid) ∧
      Accepted (Numerics.outputs ratio true (middleGrid ratio grid)) ∧
      next = stepGrid ratio grid := by
  unfold Numerics.step at h
  dsimp only at h
  split at h
  · rename_i hx
    split at h
    · rename_i hy
      exact ⟨hx, hy, (Option.some.inj h).symm⟩
    · contradiction
  · contradiction

noncomputable def stepBoundary {n : Nat} (hn : 0 < n) (ratio : UInt64)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  gridBoundary hn false ratio grid i + gridBoundary hn true ratio (middleGrid ratio grid) i

noncomputable def stepResidual {n : Nat} (hn : 0 < n) (ratio : UInt64)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  gridResidual hn false ratio grid i + gridResidual hn true ratio (middleGrid ratio grid) i

noncomputable def stepErrorBound {n : Nat} (hn : 0 < n) (ratio : UInt64)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  gridErrorBound hn false ratio grid i + gridErrorBound hn true ratio (middleGrid ratio grid) i

theorem accepted_step_balance {n : Nat} (hn : 0 < n) (ratio : UInt64)
    (grid next : Grid n n) (h : Numerics.step ratio grid = some next) (i : Fin 4) :
    gridTotal hn next i - gridTotal hn grid i =
      stepBoundary hn ratio grid i + stepResidual hn ratio grid i := by
  obtain ⟨hx, hy, rfl⟩ := accepted_step_parts ratio grid next h
  have bx := accepted_grid_balance hn false ratio grid hx i
  have by' := accepted_grid_balance hn true ratio (middleGrid ratio grid) hy i
  change gridTotal hn (middleGrid ratio grid) i - gridTotal hn grid i = _ at bx
  change gridTotal hn (stepGrid ratio grid) i - gridTotal hn (middleGrid ratio grid) i = _ at by'
  unfold stepBoundary stepResidual
  linarith only [bx, by']

theorem accepted_step_residual_bound {n : Nat} (hn : 0 < n) (ratio : UInt64)
    (grid next : Grid n n) (h : Numerics.step ratio grid = some next) (i : Fin 4) :
    |stepResidual hn ratio grid i| ≤ stepErrorBound hn ratio grid i := by
  obtain ⟨hx, hy, _⟩ := accepted_step_parts ratio grid next h
  exact le_trans (abs_add_le _ _) (add_le_add
    (accepted_grid_residual_bound hn false ratio grid hx i)
    (accepted_grid_residual_bound hn true ratio (middleGrid ratio grid) hy i))

#print axioms accepted_step_parts
#print axioms accepted_step_balance
#print axioms accepted_step_residual_bound
end Project.EulerRiemann.Frozen.Conservation
