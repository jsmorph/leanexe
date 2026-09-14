import Project.EulerOutwardMaximum.Program
import Project.EulerOutwardSpeed.Speed

namespace Project.EulerOutwardMaximum.Execution
open Wasm Project.FunctionRegion
open Project.EulerOutwardSpeed.Execution (checkedValues)
open Project.EulerRiemann.OutwardSpeed (speedUpper)

def speedDomain (index : Nat) : Prop := index ≤ 36

def speedRename (index : Nat) : Nat :=
  if index ≤ 21 then index + 4
  else if index = 22 then 2
  else if index ≤ 25 then index + 3
  else if index = 26 then 0
  else if index = 27 then 29
  else if index = 28 then 1
  else index + 1

theorem speedShift :
    Shift Project.EulerOutwardSpeed.«module» Project.EulerOutwardMaximum.«module»
      speedRename speedRename speedDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  have hi : index ≤ 36 := hi
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [speedDomain]

theorem speed_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerOutwardMaximum.«module» 37 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ values = checkedValues (speedUpper rho mx my energy)) :=
  Project.FunctionRegion.terminatesWith speedShift 36 (by norm_num [speedDomain])
    (Project.EulerOutwardSpeed.Execution.speed_exact env initial rho mx my energy)

theorem rejected_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerOutwardMaximum.«module» 2 initial []
      (fun final values => final = initial ∧ values = [.i64 0, .i64 1]) :=
  Project.FunctionRegion.terminatesWith speedShift 22 (by norm_num [speedDomain])
    (Project.EulerOutwardSpeed.Execution.rejected_exact env initial)

#print axioms speedShift
#print axioms speed_exact
#print axioms rejected_exact
end Project.EulerOutwardMaximum.Execution
