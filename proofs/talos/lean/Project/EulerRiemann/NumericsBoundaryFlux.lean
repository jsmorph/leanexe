import Project.EulerRiemann.NumericsLineBalance
import Project.EulerRiemann.NumericsInterfaceResidual

namespace Project.EulerRiemann.Conservation
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep
open Project.Euler2DConservative.Guard (decodedState)
open Numerics (rowCellFlux fluxWords)

def constantFlux (q : State) : Project.Euler2DDynamicFlux.Model.CheckedFlux :=
  Numerics.fluxCheckedBits q.density q.mx q.my q.energy q.density q.mx q.my q.energy

noncomputable def physicalStateFlux (q : State) (i : Fin 4) : ℝ :=
  RealRusanov.physicalFlux (decodedState q.density q.mx q.my q.energy) i

noncomputable def constantFluxErrorBound (q : State) (i : Fin 4) : ℝ :=
  Numerics.interfaceErrorBounds q.density q.mx q.my q.energy q.density q.mx q.my q.energy i

theorem constant_flux_reference_bound (q : State) (h : (constantFlux q).status = 0) (i : Fin 4) :
    |value (fluxWords (constantFlux q) i) - physicalStateFlux q i| ≤ constantFluxErrorBound q i := by
  have hb := Numerics.accepted_interface_reference_bound
    q.density q.mx q.my q.energy q.density q.mx q.my q.energy h i
  dsimp only at hb
  have he : RealRusanov.interfaceFlux (value (constantFlux q).alpha)
      (decodedState q.density q.mx q.my q.energy)
      (decodedState q.density q.mx q.my q.energy) i = physicalStateFlux q i := by
    unfold RealRusanov.interfaceFlux physicalStateFlux
    ring
  unfold constantFlux at he
  rw [he] at hb
  exact hb

theorem line_terminal {n : Nat} (hn : 0 < n) (axis : Bool) (grid : Grid n n) (line : Fin n) :
    lineState hn axis grid line n = lineState hn axis grid line (n - 1) := by
  have hc : clamp hn n = clamp hn (n - 1) := by
    apply Fin.ext
    simp only [clamp]
    omega
  simp only [lineState, hc]

theorem line_left_flux {n : Nat} (hn : 0 < n) (axis : Bool) (grid : Grid n n) (line : Fin n) :
    rowCellFlux (lineState hn axis grid line) 0 = constantFlux (lineState hn axis grid line 0) := rfl

theorem line_right_flux {n : Nat} (hn : 0 < n) (axis : Bool) (grid : Grid n n) (line : Fin n) :
    rowCellFlux (lineState hn axis grid line) n =
      constantFlux (lineState hn axis grid line (n - 1)) := by
  unfold rowCellFlux Numerics.leftFlux Numerics.rowCellInputs
  rw [line_terminal hn axis grid line]
  rfl

theorem line_boundary_accepted {n : Nat} (hn : 0 < n) (axis : Bool) (ratio : UInt64)
    (grid : Grid n n) (h : Accepted (Numerics.outputs ratio axis grid)) (line : Fin n) :
    (constantFlux (lineState hn axis grid line 0)).status = 0 ∧
      (constantFlux (lineState hn axis grid line (n - 1))).status = 0 := by
  have hl := (Numerics.accepted_cell_update ratio _
    (line_accepted hn axis ratio grid h line 0 hn) 0).1
  have hr := (Numerics.accepted_cell_update ratio _
    (line_accepted hn axis ratio grid h line (n - 1) (by omega)) 0).2.1
  change (rowCellFlux (lineState hn axis grid line) 0).status = 0 at hl
  rw [Numerics.row_right_flux, show n - 1 + 1 = n by omega] at hr
  rw [line_left_flux] at hl
  rw [line_right_flux] at hr
  exact ⟨hl, hr⟩

#print axioms constant_flux_reference_bound
#print axioms line_boundary_accepted
end Project.EulerRiemann.Conservation
