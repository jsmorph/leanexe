import Project.EulerRiemann.NumericsPhysicalBoundary

namespace Project.EulerRiemann.Conservation
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep

noncomputable def physicalTotal {n : Nat} (hn : 0 < n) (grid : Grid n n) (i : Fin 4) : ℝ :=
  gridTotal hn grid i / (n : ℝ) ^ 2

noncomputable def stepPhysicalBoundary {n : Nat} (hn : 0 < n) (dt : UInt64)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  let ratio := Wasm.IEEE64.div dt (Time.spacing n)
  value dt / (n : ℝ) * (gridPhysicalFlux hn false grid i +
    gridPhysicalFlux hn true (middleGrid ratio grid) i)

noncomputable def stepPhysicalResidual {n : Nat} (hn : 0 < n) (dt : UInt64)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  let ratio := Wasm.IEEE64.div dt (Time.spacing n)
  (stepResidual hn ratio grid i + gridPhysicalResidual hn false ratio dt grid i +
    gridPhysicalResidual hn true ratio dt (middleGrid ratio grid) i) / (n : ℝ) ^ 2

noncomputable def stepPhysicalErrorBound {n : Nat} (hn : 0 < n) (dt : UInt64)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  let ratio := Wasm.IEEE64.div dt (Time.spacing n)
  (stepErrorBound hn ratio grid i + gridPhysicalErrorBound hn false ratio dt grid i +
    gridPhysicalErrorBound hn true ratio dt (middleGrid ratio grid) i) / (n : ℝ) ^ 2

theorem step_physical_balance {n : Nat} (hn : 0 < n) (dt : UInt64) (grid next : Grid n n)
    (h : Numerics.step (Wasm.IEEE64.div dt (Time.spacing n)) grid = some next) (i : Fin 4) :
    physicalTotal hn next i - physicalTotal hn grid i =
      stepPhysicalBoundary hn dt grid i + stepPhysicalResidual hn dt grid i := by
  let ratio := Wasm.IEEE64.div dt (Time.spacing n)
  have hb := accepted_step_balance hn ratio grid next h i
  have he : gridTotal hn next i - gridTotal hn grid i =
      value dt * (n : ℝ) * (gridPhysicalFlux hn false grid i +
        gridPhysicalFlux hn true (middleGrid ratio grid) i) +
      (stepResidual hn ratio grid i + gridPhysicalResidual hn false ratio dt grid i +
        gridPhysicalResidual hn true ratio dt (middleGrid ratio grid) i) := by
    rw [hb]
    unfold stepBoundary gridPhysicalResidual
    ring
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold physicalTotal stepPhysicalBoundary stepPhysicalResidual
  dsimp only
  rw [← sub_div, he]
  dsimp only [ratio]
  field_simp [hnR]

theorem step_physical_residual_bound {n : Nat} (hn : 0 < n) (hsize : 2 ≤ n ∧ n ≤ 800)
    (time dt : UInt64) (grid next : Grid n n) (ht : Time.validAdvance time dt = true)
    (h : Numerics.step (Wasm.IEEE64.div dt (Time.spacing n)) grid = some next) (i : Fin 4) :
    |stepPhysicalResidual hn dt grid i| ≤ stepPhysicalErrorBound hn dt grid i := by
  let ratio := Wasm.IEEE64.div dt (Time.spacing n)
  obtain ⟨hx, hy, _⟩ := accepted_step_parts ratio grid next h
  have hr := accepted_ratio_error hsize time dt grid next ht h
  have bu := accepted_step_residual_bound hn ratio grid next h i
  have bx := grid_physical_residual_bound hn false ratio dt grid hx hr i
  have by' := grid_physical_residual_bound hn true ratio dt (middleGrid ratio grid) hy hr i
  unfold stepPhysicalResidual stepPhysicalErrorBound
  dsimp only
  rw [abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg (n : ℝ))
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add bu bx) by')

#print axioms step_physical_balance
#print axioms step_physical_residual_bound
end Project.EulerRiemann.Conservation
