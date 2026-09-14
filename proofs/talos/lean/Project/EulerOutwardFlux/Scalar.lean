import Project.EulerOutwardFlux.Program
import Project.EulerOutwardSpeed.Speed
import Project.EulerRiemann.ExecutionScalar

namespace Project.EulerOutwardFlux.Execution
open Wasm Project.FunctionRegion
open Project.EulerConservative.Execution (boolWord)
open Project.EulerOutwardSpeed.Execution (checkedValues)

def speedDomain (index : Nat) : Prop := index ≤ 36

theorem speedShift :
    Shift Project.EulerOutwardSpeed.«module» Project.EulerOutwardFlux.«module»
      id id speedDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  have hi : index ≤ 36 := hi
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [speedDomain]

theorem speed_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerOutwardFlux.«module» 36 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ values =
        checkedValues (Project.EulerRiemann.OutwardSpeed.speedUpper rho mx my energy)) :=
  Project.FunctionRegion.terminatesWith speedShift 36 (by norm_num [speedDomain])
    (Project.EulerOutwardSpeed.Execution.speed_exact env initial rho mx my energy)

def scalarDomain (index : Nat) : Prop :=
  index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 21 ∨ 41 ≤ index ∧ index ≤ 46

def scalarRename (index : Nat) : Nat :=
  if index ≤ 4 then index - 2 else if index = 21 then 37 else index

theorem scalarShift :
    Shift Project.EulerRiemann.«module» Project.EulerOutwardFlux.«module»
      scalarRename scalarRename scalarDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  rcases hi with rfl | rfl | rfl | rfl | ⟨hlo, hhi⟩
  all_goals try interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [scalarDomain]

theorem side_positive_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerOutwardFlux.«module» 0 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.Euler2DConservative.Model.positiveBits word))]) :=
  Project.FunctionRegion.terminatesWith scalarShift 2 (by norm_num [scalarDomain])
    (Project.EulerRiemann.Execution.side_positive_exact env initial word)

theorem side_finite_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerOutwardFlux.«module» 2 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.Euler2DConservative.Model.finiteBits word))]) :=
  Project.FunctionRegion.terminatesWith scalarShift 4 (by norm_num [scalarDomain])
    (Project.EulerRiemann.Execution.side_finite_exact env initial word)

theorem rejected_side_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerOutwardFlux.«module» 37 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) :=
  Project.FunctionRegion.terminatesWith scalarShift 21 (by norm_num [scalarDomain])
    (Project.EulerRiemann.Execution.rejected_side_exact env initial)

theorem component_exact (env : HostEnv Unit) (initial : Store Unit)
    (alpha fluxL fluxR stateL stateR : UInt64) :
    TerminatesWith env Project.EulerOutwardFlux.«module» 46 initial
      [.i64 stateR, .i64 stateL, .i64 fluxR, .i64 fluxL, .i64 alpha]
      (fun final values => final = initial ∧
        values = Project.EulerDynamicFlux.Execution.componentValues alpha fluxL fluxR stateL stateR) :=
  Project.FunctionRegion.terminatesWith scalarShift 46 (by norm_num [scalarDomain])
    (Project.EulerRiemann.Execution.component_exact env initial alpha fluxL fluxR stateL stateR)

#print axioms speedShift
#print axioms speed_exact
#print axioms scalarShift
#print axioms side_positive_exact
#print axioms side_finite_exact
#print axioms rejected_side_exact
#print axioms component_exact
end Project.EulerOutwardFlux.Execution
