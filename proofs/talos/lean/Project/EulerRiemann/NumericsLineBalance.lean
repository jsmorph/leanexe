import Project.EulerRiemann.NumericsLineGeometry

namespace Project.EulerRiemann.Conservation
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep
open Numerics (rowCellInputs rowCellFlux stateWords fluxWords)
open scoped BigOperators

noncomputable def stateValue (q : State) (i : Fin 4) : ℝ :=
  value (stateWords q.density q.mx q.my q.energy i)

noncomputable def lineTotal {n : Nat} (hn : 0 < n) (axis : Bool) (grid : Grid n n)
    (line : Fin n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, stateValue (lineState hn axis grid line k) i

noncomputable def lineBoundary {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (line : Fin n) (i : Fin 4) : ℝ :=
  value ratio * (value (fluxWords (rowCellFlux (lineState hn axis grid line) 0) i) -
    value (fluxWords (rowCellFlux (lineState hn axis grid line) n) i))

noncomputable def lineResidual {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (line : Fin n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, Numerics.cellUpdateResidual ratio
    (rowCellInputs (lineState hn axis grid line) k) i

noncomputable def lineErrorBound {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (line : Fin n) (i : Fin 4) : ℝ :=
  ∑ k ∈ Finset.range n, Numerics.cellUpdateErrorBound ratio
    (rowCellInputs (lineState hn axis grid line) k) i

theorem accepted_line_balance {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs ratio axis grid))
    (line : Fin n) (i : Fin 4) :
    lineTotal hn axis (nextGrid axis (Numerics.outputs ratio axis grid)) line i -
      lineTotal hn axis grid line i = lineBoundary hn axis ratio grid line i +
        lineResidual hn axis ratio grid line i := by
  have hout : lineTotal hn axis (nextGrid axis (Numerics.outputs ratio axis grid)) line i =
      ∑ k ∈ Finset.range n, value (Numerics.cellWords (Numerics.evaluate ratio
        (rowCellInputs (lineState hn axis grid line) k)) i) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact congrArg value (line_next_words hn axis ratio grid line k (Finset.mem_range.mp hk) i)
  rw [hout]
  exact Numerics.accepted_cell_row_balance n ratio (lineState hn axis grid line)
    (line_accepted hn axis ratio grid h line) i

theorem accepted_line_residual_bound {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs ratio axis grid))
    (line : Fin n) (i : Fin 4) :
    |lineResidual hn axis ratio grid line i| ≤ lineErrorBound hn axis ratio grid line i :=
  Numerics.accepted_cell_row_residual_bound n ratio (lineState hn axis grid line)
    (line_accepted hn axis ratio grid h line) i

#print axioms accepted_line_balance
#print axioms accepted_line_residual_bound
end Project.EulerRiemann.Conservation
