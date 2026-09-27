import Project.SequenceSoftmax.Program
import Project.Softmax.ExecutionBase
import Project.ExpNeg.Execution
import Project.FunctionRegion.Exec
import Mathlib.Tactic

namespace Project.SequenceSoftmax
open Project.FunctionRegion

theorem maximumRegion : Shift Project.Softmax.module module
    (fun _ => 7) (fun _ => 7) (fun i => i = 2) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rintro i rfl
  refine ⟨_, rfl, rfl, ?_⟩
  prove_portable

theorem exponentialRegion : Shift Project.ExpNeg.module module
    (fun i => i-1) (fun i => i-1) (fun i => 1 ≤ i ∧ i ≤ 6) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rintro i ⟨hLower, hUpper⟩
  interval_cases i
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

namespace Spec
open Wasm

theorem scalarMaximum_exact (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64) :
    TerminatesWith env module 7 initial [.i64 b, .i64 a]
      (fun final values => final = initial ∧ values = [.i64 (Softmax.maximum a b)]) :=
  Project.FunctionRegion.terminatesWith maximumRegion 2 rfl
    (Softmax.Spec.maximum_exact env initial a b)

theorem exponential_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env module 5 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (ExpNeg.evaluate x)]) :=
  Project.FunctionRegion.terminatesWith exponentialRegion 6 (by decide)
    (ExpNeg.Spec.evaluate_exact env initial x)

#print axioms scalarMaximum_exact
#print axioms exponential_exact
end Spec
end Project.SequenceSoftmax
