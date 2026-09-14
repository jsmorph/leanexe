import Project.Euler2DConservative.RealHyperbolicity
import Project.EulerRiemann.ControlSafe
import Project.EulerRiemann.ControlTrace

namespace Project.EulerRiemann.Hyperbolicity
open Project.Euler2DCellStep.Sweep
open Project.Euler2DConservative
open Project.Euler2DConservative.RealFlux

noncomputable def StateHyperbolic (q : State) : Prop :=
  Hyperbolic (Guard.decodedState q.density q.mx q.my q.energy)

theorem state_hyperbolic (q : State) (h : StateSafe q) : StateHyperbolic q :=
  admissible_hyperbolic _ h.2

theorem accepted_side_hyperbolic (rho mx my energy : UInt64)
    (h : (Numerics.sideCheckedBits rho mx my energy).status = 0) :
    Hyperbolic (Guard.decodedState rho mx my energy) :=
  admissible_hyperbolic _ (Numerics.side_state rho mx my energy h).admissible

noncomputable def GridHyperbolic {nx ny : Nat} (grid : Grid nx ny) : Prop :=
  ∀ j i, StateHyperbolic (grid j i)

theorem grid_hyperbolic {nx ny : Nat} (grid : Grid nx ny) (h : GridSafe grid) :
    GridHyperbolic grid := fun j i => state_hyperbolic _ (h j i)

theorem step_grids_safe {nx ny : Nat} (ratio : UInt64) (grid next : Grid nx ny)
    (h : Numerics.step ratio grid = some next) :
    GridSafe (nextGrid false (Numerics.outputs ratio false grid)) ∧ GridSafe next := by
  dsimp only [Numerics.step] at h
  split at h
  · rename_i hx
    split at h
    · rename_i hy
      cases h
      exact ⟨Numerics.nextGrid_safe _ _ _ hx, Numerics.nextGrid_safe _ _ _ hy⟩
    · cases h
  · cases h

theorem step_grids_hyperbolic {nx ny : Nat} (ratio : UInt64) (grid next : Grid nx ny)
    (h : Numerics.step ratio grid = some next) :
    GridHyperbolic (nextGrid false (Numerics.outputs ratio false grid)) ∧
      GridHyperbolic next :=
  ⟨grid_hyperbolic _ (step_grids_safe ratio grid next h).1,
    grid_hyperbolic _ (step_grids_safe ratio grid next h).2⟩

theorem trace_safe {n : Nat} {time finalTime : UInt64} {grid finalGrid : Grid n n}
    {dts : List UInt64} (ht : Control.NumericalTrace n time grid dts finalTime finalGrid)
    (hs : GridSafe grid) : GridSafe finalGrid := by
  revert hs
  induction ht with
  | nil => exact id
  | cons _ hstep _ ih =>
    intro _
    exact ih (step_grids_safe _ _ _ hstep).2

noncomputable def TraceHyperbolic (n : Nat) : Prop :=
  ∀ time grid dts, Control.NumericalTrace n 0 (Initial.initial n) dts time grid →
    GridHyperbolic grid ∧
      ∀ ratio next, Numerics.step ratio grid = some next →
        GridHyperbolic (nextGrid false (Numerics.outputs ratio false grid)) ∧
          GridHyperbolic next

theorem initial_trace_hyperbolic (n : Nat) : TraceHyperbolic n := by
  intro time grid dts ht
  exact ⟨grid_hyperbolic _ (trace_safe ht (Initial.initial_safe n)),
    fun ratio next hs => step_grids_hyperbolic ratio grid next hs⟩

noncomputable def CellsHyperbolic (grid : Array Traversal.Cell) : Prop :=
  ∀ i (hi : i < grid.size), StateHyperbolic grid[i].state

theorem cells_hyperbolic (grid : Array Traversal.Cell) (h : Control.CellsSafe grid) :
    CellsHyperbolic grid := fun i hi => state_hyperbolic _ (h i hi)

theorem run_hyperbolic (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    CellsHyperbolic (Control.run n).grid :=
  cells_hyperbolic _ (Control.run_safe n hn)

#print axioms accepted_side_hyperbolic
#print axioms step_grids_hyperbolic
#print axioms initial_trace_hyperbolic
#print axioms run_hyperbolic

end Project.EulerRiemann.Hyperbolicity
