import Project.EulerRiemann.FrozenNumericsSweep
import Project.EulerRiemann.FrozenNumericsUpdateResidual
import Project.EulerRiemann.FrozenNumericsVectors

namespace Project.EulerRiemann.Frozen.Numerics
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (Inputs)
open Project.EulerCellStep.Model (updateCheckedBits)
open Project.ProofKit.F64RoundingResidual (radius)

def cellWords (cell : Project.Euler2DCellStep.Model.CheckedCell) : Fin 4 → UInt64 :=
  ![cell.density, cell.momentum, cell.transverse, cell.energy]

def leftFlux (q : Inputs) : Project.Euler2DDynamicFlux.Model.CheckedFlux :=
  fluxCheckedBits q.left.density q.left.mx q.left.my q.left.energy
    q.center.density q.center.mx q.center.my q.center.energy

def rightFlux (q : Inputs) : Project.Euler2DDynamicFlux.Model.CheckedFlux :=
  fluxCheckedBits q.center.density q.center.mx q.center.my q.center.energy
    q.right.density q.right.mx q.right.my q.right.energy

theorem accepted_cell_update (ratio : UInt64) (q : Inputs)
    (h : (evaluate ratio q).status = 0) (i : Fin 4) :
    let state := stateWords q.center.density q.center.mx q.center.my q.center.energy i
    let next := updateCheckedBits ratio state (fluxWords (leftFlux q) i) (fluxWords (rightFlux q) i)
    (leftFlux q).status = 0 ∧ (rightFlux q).status = 0 ∧
      next.status = 0 ∧ cellWords (evaluate ratio q) i = next.value := by
  unfold leftFlux rightFlux
  unfold evaluate cellCheckedBits at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all [Project.Euler2DCellStep.Model.rejectedCell]
  all_goals fin_cases i <;> simp_all [cellWords, stateWords, fluxWords]

noncomputable def cellUpdateResidual (ratio : UInt64) (q : Inputs) (i : Fin 4) : ℝ :=
  Project.ProofKit.F64ConservativeUpdate.residual ratio
    (stateWords q.center.density q.center.mx q.center.my q.center.energy i)
    (fluxWords (leftFlux q) i) (fluxWords (rightFlux q) i) (cellWords (evaluate ratio q) i)

noncomputable def cellUpdateErrorBound (ratio : UInt64) (q : Inputs) (i : Fin 4) : ℝ :=
  let difference := Wasm.IEEE64.sub (fluxWords (rightFlux q) i) (fluxWords (leftFlux q) i)
  |value ratio| * radius difference + radius (Wasm.IEEE64.mul ratio difference) +
    radius (cellWords (evaluate ratio q) i)

theorem accepted_cell_balance (ratio : UInt64) (q : Inputs)
    (h : (evaluate ratio q).status = 0) (i : Fin 4) :
    let state := stateWords q.center.density q.center.mx q.center.my q.center.energy i
    let left := fluxWords (leftFlux q) i
    let right := fluxWords (rightFlux q) i
    let out := cellWords (evaluate ratio q) i
    Project.ProofKit.F64ConservativeUpdate.Certificate ratio state left right out ∧
      value out - value state = value ratio * (value left - value right) + cellUpdateResidual ratio q i ∧
      |cellUpdateResidual ratio q i| ≤ cellUpdateErrorBound ratio q i := by
  obtain ⟨_, _, hNext, hValue⟩ := accepted_cell_update ratio q h i
  dsimp only
  refine ⟨?_, Project.ProofKit.F64ConservativeUpdate.balance _ _ _ _ _, ?_⟩
  · rw [hValue]
    exact accepted_update_certificate _ _ _ _ hNext
  · unfold cellUpdateResidual cellUpdateErrorBound
    rw [hValue]
    exact accepted_update_residual_bound _ _ _ _ hNext

#print axioms accepted_cell_update
#print axioms accepted_cell_balance
end Project.EulerRiemann.Frozen.Numerics
