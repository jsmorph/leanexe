import Project.EulerCertificate.SolverRegion
import Project.EulerReconstructed.RiemannRegion
import Project.EulerRiemann.ExecutionOutput

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime
open Project.EulerRiemann Project.EulerRiemann.Execution

theorem output_budget_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n spare pageLimit : Nat) (time status : UInt64)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid) (hSize : grid.size ≤ 640000)
    (hBudget : OutputBudget initial heap (outputBytes grid.size + spare) pageLimit) :
    TerminatesWith env Project.EulerCertificate.«module» 3 initial
      [.i64 source.root, .i64 source.root, .i64 status, .i64 time, .i64 (UInt64.ofNat n)]
      (fun final values => ∃ (finalHeap : Heap) (result : FreeNode),
        values = [.i64 result.root, .i64 result.root] ∧ finalHeap.At final ∧
        finalHeap.OwnsWords final result (Output.pack n time status grid) ∧
        OutputBudget final finalHeap spare pageLimit) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 144 (by norm_num [SolverRegion.domain])
    (Project.FunctionRegion.terminatesWith Project.EulerReconstructed.RiemannRegion.shift 99
      (by norm_num [Project.EulerReconstructed.RiemannRegion.domain])
      (Project.EulerRiemann.Execution.output_budget_exact env initial heap source grid n spare pageLimit
        time status hHeap hOwner hSize hBudget))

#print axioms output_budget_exact
end Project.EulerCertificate.Execution
