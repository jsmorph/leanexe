import Project.EulerRiemann.FrozenNumericsCellResidual
import Project.ProofKit.RealFiniteVolumeBalance

namespace Project.EulerRiemann.Frozen.Numerics
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (Inputs State)
open scoped BigOperators

def rowCellInputs (state : Nat → State) (k : Nat) : Inputs :=
  ⟨state (k - 1), state k, state (k + 1)⟩

def rowCellFlux (state : Nat → State) (k : Nat) : Project.Euler2DDynamicFlux.Model.CheckedFlux :=
  leftFlux (rowCellInputs state k)

theorem row_right_flux (state : Nat → State) (k : Nat) :
    rightFlux (rowCellInputs state k) = rowCellFlux state (k + 1) := by
  simp [rightFlux, rowCellFlux, leftFlux, rowCellInputs]

theorem accepted_cell_row_balance (count : Nat) (ratio : UInt64) (state : Nat → State)
    (h : ∀ k < count, (evaluate ratio (rowCellInputs state k)).status = 0) (i : Fin 4) :
    (∑ k ∈ Finset.range count, value (cellWords (evaluate ratio (rowCellInputs state k)) i)) -
      (∑ k ∈ Finset.range count, value (stateWords (state k).density (state k).mx (state k).my (state k).energy i)) =
      value ratio * (value (fluxWords (rowCellFlux state 0) i) - value (fluxWords (rowCellFlux state count) i)) +
        ∑ k ∈ Finset.range count, cellUpdateResidual ratio (rowCellInputs state k) i := by
  rw [show value ratio * (value (fluxWords (rowCellFlux state 0) i) -
      value (fluxWords (rowCellFlux state count) i)) =
      -value ratio * (value (fluxWords (rowCellFlux state count) i) -
        value (fluxWords (rowCellFlux state 0) i)) by ring]
  apply Project.ProofKit.RealFiniteVolumeBalance.sweep_balance count (value ratio)
    (fun k => value (stateWords (state k).density (state k).mx (state k).my (state k).energy i))
    (fun k => value (cellWords (evaluate ratio (rowCellInputs state k)) i))
    (fun k => value (fluxWords (rowCellFlux state k) i))
    (fun k => cellUpdateResidual ratio (rowCellInputs state k) i)
  intro k hk
  have balance := (accepted_cell_balance ratio (rowCellInputs state k) (h k hk) i).2.1
  dsimp only [rowCellInputs] at balance
  have right := row_right_flux state k
  dsimp only [rowCellInputs] at right
  rw [right] at balance
  change value (cellWords (evaluate ratio (rowCellInputs state k)) i) -
      value (stateWords (state k).density (state k).mx (state k).my (state k).energy i) =
      value ratio * (value (fluxWords (rowCellFlux state k) i) -
        value (fluxWords (rowCellFlux state (k + 1)) i)) +
      cellUpdateResidual ratio (rowCellInputs state k) i at balance
  linarith only [balance]

theorem accepted_cell_row_residual_bound (count : Nat) (ratio : UInt64) (state : Nat → State)
    (h : ∀ k < count, (evaluate ratio (rowCellInputs state k)).status = 0) (i : Fin 4) :
    |∑ k ∈ Finset.range count, cellUpdateResidual ratio (rowCellInputs state k) i| ≤
      ∑ k ∈ Finset.range count, cellUpdateErrorBound ratio (rowCellInputs state k) i := by
  calc
    _ ≤ ∑ k ∈ Finset.range count, |cellUpdateResidual ratio (rowCellInputs state k) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun k hk =>
      (accepted_cell_balance ratio (rowCellInputs state k) (h k (Finset.mem_range.mp hk)) i).2.2)

#print axioms row_right_flux
#print axioms accepted_cell_row_balance
#print axioms accepted_cell_row_residual_bound
end Project.EulerRiemann.Frozen.Numerics
