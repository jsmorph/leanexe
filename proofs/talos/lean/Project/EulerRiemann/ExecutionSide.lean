import Project.EulerRiemann.Program
import Project.Euler2DConservative.Spec
import Project.FunctionRegion.Exec

namespace Project.EulerRiemann.Execution
open Wasm Project.FunctionRegion

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def sideDomain (index : Nat) : Prop := index < 14

def sideRename (index : Nat) : Nat := index + 2

theorem sideShift :
    Shift Project.Euler2DConservative.«module» Project.EulerRiemann.«module»
      sideRename sideRename sideDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  unfold sideDomain at hi
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [sideDomain]

theorem side_exact (env : HostEnv Unit) (initial : Store Unit)
    (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 15 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧
        values = Project.Euler2DConservative.Execution.resultValues rho mx my energy) :=
  Project.FunctionRegion.terminatesWith sideShift 13 (by norm_num [sideDomain])
    (Project.Euler2DConservative.Spec.sideCheckedBits_exact env initial rho mx my energy)

#print axioms sideShift
#print axioms side_exact

end Project.EulerRiemann.Execution
