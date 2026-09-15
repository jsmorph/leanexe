import Project.EulerReconstructed.RiemannRegion
import Project.EulerRiemann.ExecutionTimeGuard
import Project.EulerRiemann.ExecutionProposal

namespace Project.EulerReconstructed.Execution
open Wasm Project.EulerRiemann
open Project.EulerRiemann.Execution (boolWord)

theorem endTime_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerReconstructed.«module» 0 initial []
      (fun final values => final = initial ∧ values = [.i64 Time.endTime]) :=
  Project.FunctionRegion.terminatesWith RiemannRegion.shift 0
    (by norm_num [RiemannRegion.domain])
    (Project.EulerRiemann.Execution.endTime_exact env initial)

theorem validAdvance_exact (env : HostEnv Unit) (initial : Store Unit) (time dt : UInt64) :
    TerminatesWith env Project.EulerReconstructed.«module» 50 initial [.i64 dt, .i64 time]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (Time.validAdvance time dt))]) :=
  Project.FunctionRegion.terminatesWith RiemannRegion.shift 36
    (by norm_num [RiemannRegion.domain])
    (Project.EulerRiemann.Execution.validAdvance_exact env initial time dt)

theorem proposal_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (time alpha : UInt64) (hn : n ≤ 800) :
    TerminatesWith env Project.EulerReconstructed.«module» 49 initial
      [.i64 alpha, .i64 time, .i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧ values = [.i64 (Time.proposal n time alpha)]) :=
  Project.FunctionRegion.terminatesWith RiemannRegion.shift 35
    (by norm_num [RiemannRegion.domain])
    (Project.EulerRiemann.Execution.proposal_exact env initial n time alpha hn)

#print axioms endTime_exact
#print axioms validAdvance_exact
#print axioms proposal_exact
end Project.EulerReconstructed.Execution
