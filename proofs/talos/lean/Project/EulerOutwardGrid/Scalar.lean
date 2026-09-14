import Project.EulerOutwardGrid.Program
import Project.EulerOutwardMaximum.Merge

namespace Project.EulerOutwardGrid.Execution
open Wasm Project.FunctionRegion
open Project.EulerOutwardSpeed.Execution (checkedValues)
open Project.EulerRiemann.OutwardSpeed (speedUpper)
open Project.EulerRiemann.OutwardMaximum (merge)
open Project.ProofKit.F64Outward (Checked)

def scalarDomain (index : Nat) : Prop := index ≤ 41

theorem scalarShift :
    Shift Project.EulerOutwardMaximum.«module» Project.EulerOutwardGrid.«module»
      id id scalarDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  have hi : index ≤ 41 := hi
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [scalarDomain]

theorem speed_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerOutwardGrid.«module» 37 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ values = checkedValues (speedUpper rho mx my energy)) :=
  Project.FunctionRegion.terminatesWith scalarShift 37 (by norm_num [scalarDomain])
    (Project.EulerOutwardMaximum.Execution.speed_exact env initial rho mx my energy)

theorem merge_exact (env : HostEnv Unit) (initial : Store Unit) (left right : Checked) :
    TerminatesWith env Project.EulerOutwardGrid.«module» 3 initial
      [.i64 right.value, .i64 right.status, .i64 left.value, .i64 left.status]
      (fun final values => final = initial ∧ values = checkedValues (merge left right)) :=
  Project.FunctionRegion.terminatesWith scalarShift 3 (by norm_num [scalarDomain])
    (Project.EulerOutwardMaximum.Execution.merge_exact env initial left right)

#print axioms scalarShift
#print axioms speed_exact
#print axioms merge_exact
end Project.EulerOutwardGrid.Execution
