import Project.EulerRiemann.NumericsLineBalance

namespace Project.EulerRiemann.Conservation
open Project.Euler2DCellStep.Sweep
open scoped BigOperators

def normalComponent (axis : Bool) (i : Fin 4) : Fin 4 :=
  if axis then ![0, 2, 1, 3] i else i

theorem stateValue_orient (axis : Bool) (q : State) (i : Fin 4) :
    stateValue (orient axis q) (normalComponent axis i) = stateValue q i := by
  cases axis <;> fin_cases i <;> rfl

noncomputable def gridTotal {n : Nat} (hn : 0 < n) (grid : Grid n n) (i : Fin 4) : ℝ :=
  ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
    stateValue (grid (clamp hn j) (clamp hn k)) i

theorem gridTotal_as_lines {n : Nat} (hn : 0 < n) (axis : Bool)
    (grid : Grid n n) (i : Fin 4) :
    gridTotal hn grid i = ∑ k ∈ Finset.range n,
      lineTotal hn axis grid (clamp hn k) (normalComponent axis i) := by
  cases axis with
  | false => rfl
  | true =>
    unfold gridTotal
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    unfold lineTotal
    apply Finset.sum_congr rfl
    intro j _
    exact (stateValue_orient true (grid (clamp hn j) (clamp hn k)) i).symm

noncomputable def gridBoundary {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, lineBoundary hn axis ratio grid (clamp hn k) (normalComponent axis i)

noncomputable def gridResidual {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, lineResidual hn axis ratio grid (clamp hn k) (normalComponent axis i)

noncomputable def gridErrorBound {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, lineErrorBound hn axis ratio grid (clamp hn k) (normalComponent axis i)

theorem accepted_grid_balance {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs ratio axis grid)) (i : Fin 4) :
    gridTotal hn (nextGrid axis (Numerics.outputs ratio axis grid)) i - gridTotal hn grid i =
      gridBoundary hn axis ratio grid i + gridResidual hn axis ratio grid i := by
  rw [gridTotal_as_lines hn axis, gridTotal_as_lines hn axis]
  unfold gridBoundary gridResidual
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ =>
    accepted_line_balance hn axis ratio grid h (clamp hn k) (normalComponent axis i))

theorem accepted_grid_residual_bound {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs ratio axis grid)) (i : Fin 4) :
    |gridResidual hn axis ratio grid i| ≤ gridErrorBound hn axis ratio grid i := by
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        |lineResidual hn axis ratio grid (clamp hn k) (normalComponent axis i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun k _ =>
      accepted_line_residual_bound hn axis ratio grid h (clamp hn k) (normalComponent axis i))

#print axioms gridTotal_as_lines
#print axioms accepted_grid_balance
#print axioms accepted_grid_residual_bound
end Project.EulerRiemann.Conservation
