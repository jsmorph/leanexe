import Project.EulerReconstruction.Program
import Project.EulerReconstruction.AnnotationMatches
import Project.EulerOutwardSpeed.Guard

namespace Project.EulerReconstruction.Execution
open Wasm Project.FunctionRegion
open Project.EulerConservative.Execution (boolWord)

def guardDomain (index : Nat) : Prop := index ≤ 18

theorem guardShift :
    Shift Project.EulerOutwardSpeed.«module» Project.EulerReconstruction.«module»
      id id guardDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  unfold guardDomain at hi
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [guardDomain]

theorem abs_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerReconstruction.«module» 5 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (Project.ProofKit.F64Order.absBits word)]) :=
  Project.FunctionRegion.terminatesWith guardShift 5 (by norm_num [guardDomain])
    (Project.EulerOutwardSpeed.Execution.abs_exact env initial word)

theorem finite_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerReconstruction.«module» 6 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.ProofKit.F64Order.finiteBits word))]) :=
  Project.FunctionRegion.terminatesWith guardShift 6 (by norm_num [guardDomain])
    (Project.EulerOutwardSpeed.Execution.finite_exact env initial word)

theorem state_guard_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerReconstruction.«module» 18 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.EulerRiemann.Numerics.stateGuard rho mx my energy))]) :=
  Project.FunctionRegion.terminatesWith guardShift 18 (by norm_num [guardDomain])
    (Project.EulerOutwardSpeed.Execution.state_guard_exact env initial rho mx my energy)

#print axioms guardShift
#print axioms abs_exact
#print axioms finite_exact
#print axioms state_guard_exact

end Project.EulerReconstruction.Execution
