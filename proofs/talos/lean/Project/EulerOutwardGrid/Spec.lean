import Project.EulerOutwardGrid.Execution
import Project.EulerRiemann.OutwardMaximumGrid

namespace Project.EulerOutwardGrid.Spec
open Wasm CodeLib.IEEE64
open Project.EulerRiemann
open Project.EulerRiemann.OutwardMaximum
open Project.Euler2DCellStep.Sweep (orient)
open Project.EulerOutwardSpeed.Execution (checkedValues)
open Project.ProofKit.F64Outward (rejected)

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (pointer : UInt64)
    (grid : Array Traversal.Cell), Memory.GridAt initial pointer grid →
    TerminatesWith env m 45 initial [.i64 pointer]
      (fun final values => final = initial ∧ values = checkedValues (gridUpper grid))

def Behavior (grid : Array Traversal.Cell) (values : List Value) : Prop :=
  values = [.i64 0, .i64 1] ∨
    ∃ alpha : UInt64, values = [.i64 alpha, .i64 0] ∧ Finite alpha ∧
      ∀ cell ∈ grid, Bounds cell.state alpha ∧ Bounds (orient true cell.state) alpha

def BehaviorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (pointer : UInt64)
    (grid : Array Traversal.Cell), Memory.GridAt initial pointer grid →
    TerminatesWith env m 45 initial [.i64 pointer]
      (fun final values => final = initial ∧ Behavior grid values)

theorem gridUpper_exact : ExactSpecFor module := by
  intro env initial pointer grid hGrid
  exact Execution.scan_exact env initial pointer grid hGrid

theorem gridUpper_behavior : BehaviorSpecFor module := by
  intro env initial pointer grid hGrid
  refine TerminatesWith.mono (gridUpper_exact env initial pointer grid hGrid) ?_
  rintro final values ⟨hfinal, rfl⟩
  refine ⟨hfinal, ?_⟩
  rcases grid_behavior grid with hr | hs
  · exact Or.inl (by simp [hr, checkedValues, rejected])
  · exact Or.inr ⟨(gridUpper grid).value,
      by simp [checkedValues, hs.1], hs.2⟩

#print axioms gridUpper_exact
#print axioms gridUpper_behavior
end Project.EulerOutwardGrid.Spec
