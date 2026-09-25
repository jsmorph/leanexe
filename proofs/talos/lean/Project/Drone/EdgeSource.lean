import LeanExe.Examples.Drone
import Mathlib.Tactic

namespace Project.Drone.Execution
open LeanExe.Examples.Drone

theorem edgeTicks_eq (r0 r1 z0 z1 u v : UInt64) :
    edgeTicks r0 r1 z0 z1 u v =
      if u + v = 0 then 840 * restSeconds (distance z0 z1)
      else if 200 < distance (u*u) (v*v) then 0
      else if 8000 < 3 * distance z0 z1 * (u+v) then 0
      else if 160000 < 6 * distance z0 z1 * (u+v) * (u+v) then 0
      else if r0 ≤ r1 then
        if 3*(u+v)*(z0-r0) < 2*u*(r1-r0) then 0 else 33600/((u+v)/5)
      else
        if 3*(u+v)*(z1-r1) < 2*v*(r0-r1) then 0 else 33600/((u+v)/5) := by
  simp only [edgeTicks, beq_iff_eq]
  rfl

#print axioms edgeTicks_eq
end Project.Drone.Execution
