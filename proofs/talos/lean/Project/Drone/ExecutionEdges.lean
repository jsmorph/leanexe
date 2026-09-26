import Project.Drone.ExecutionEdgeRest
import Project.Drone.ExecutionEdgeMoving

namespace Project.Drone.Execution
open Wasm LeanExe.Examples.Drone

theorem edgeTicks_exact (env : HostEnv Unit) (initial : Store Unit)
    (r0 r1 z0 z1 u v : UInt64) :
    TerminatesWith env «module» 9 initial
      [.i64 v, .i64 u, .i64 z1, .i64 z0, .i64 r1, .i64 r0]
      (fun final values => final = initial ∧ values = [.i64 (edgeTicks r0 r1 z0 z1 u v)]) := by
  by_cases h : u + v = 0
  · exact edgeTicks_at_rest_exact env initial r0 r1 z0 z1 u v h
  · exact edgeTicks_moving_exact env initial r0 r1 z0 z1 u v h

#print axioms edgeTicks_exact
end Project.Drone.Execution
