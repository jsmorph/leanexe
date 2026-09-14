import Project.EulerOutwardSpeed.Program
import Project.EulerRiemann.ExecutionGuard

namespace Project.EulerOutwardSpeed.Execution
open Wasm Project.FunctionRegion
open Project.EulerConservative.Execution (boolWord)

def guardDomain (index : Nat) : Prop := 2 ≤ index ∧ index ≤ 20
def guardRename (index : Nat) : Nat := index - 2

theorem guardShift :
    Shift Project.EulerRiemann.«module» Project.EulerOutwardSpeed.«module»
      guardRename guardRename guardDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  obtain ⟨hlo, hhi⟩ := hi
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [guardDomain]

theorem positive_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 4 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.ProofKit.F64Order.positiveBits word))]) :=
  Project.FunctionRegion.terminatesWith guardShift 6 (by norm_num [guardDomain])
    (Project.EulerRiemann.Execution.guard_positive_exact env initial word)

theorem abs_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 5 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (Project.ProofKit.F64Order.absBits word)]) :=
  Project.FunctionRegion.terminatesWith guardShift 7 (by norm_num [guardDomain])
    (Project.FunctionRegion.terminatesWith Project.EulerRiemann.Execution.normalizationShift
      1 (by norm_num [Project.EulerRiemann.Execution.normalizationDomain])
      (Project.Euler2DConservative.Execution.absBits_exact
        Project.Euler2DConservative.Execution.concreteHelperLayout env initial word))

theorem finite_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 6 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.ProofKit.F64Order.finiteBits word))]) :=
  Project.FunctionRegion.terminatesWith guardShift 8 (by norm_num [guardDomain])
    (Project.EulerRiemann.Execution.guard_finite_exact env initial word)

theorem state_guard_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 18 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.EulerRiemann.Numerics.stateGuard rho mx my energy))]) :=
  Project.FunctionRegion.terminatesWith guardShift 20 (by norm_num [guardDomain])
    (Project.EulerRiemann.Execution.state_guard_exact env initial rho mx my energy)

#print axioms guardShift
#print axioms positive_exact
#print axioms abs_exact
#print axioms finite_exact
#print axioms state_guard_exact
end Project.EulerOutwardSpeed.Execution
