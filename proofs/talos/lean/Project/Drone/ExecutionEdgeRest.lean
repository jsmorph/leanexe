import Project.Drone.ExecutionEdgeRestBody
import Project.Drone.EdgeSource

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone

theorem edgeTicks_at_rest_exact (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 z0 z1 u v : UInt64) (hRest : u + v = 0) :
    TerminatesWith env «module» 9 initial
      [.i64 v, .i64 u, .i64 z1, .i64 z0, .i64 r1, .i64 r0]
      (fun final values => final = initial ∧ values = [.i64 (edgeTicks r0 r1 z0 z1 u v)]) := by
  apply edgeTicks_entry env initial r0 r1 z0 z1 u v
  convert edgeRest_body env initial r0 r1 z0 z1 u v hRest using 1
  funext c
  cases c <;> simp [edgeTicks_eq, hRest]

#print axioms edgeTicks_at_rest_exact
end Project.Drone.Execution
