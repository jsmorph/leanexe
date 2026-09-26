import Project.Drone.ExecutionScalar
import Project.Drone.Initial

namespace Project.Drone.Execution
open LeanExe.Examples.Drone

def initialWord (state : Nat) : UInt64 := if state == 0 then 0 else infinity

def initialRows : Nat → Nat → Array UInt64 → Array UInt64
  | 0, _, row => row
  | count + 1, state, row =>
    initialRows count (state + 1) (((row.push (initialWord state)).push (initialWord state)).push 0)

theorem initialRows_size (count state : Nat) (row : Array UInt64) :
    (initialRows count state row).size = row.size + 3 * count := by
  induction count generalizing state row with
  | zero => rfl
  | succ count ih =>
    simp only [initialRows, ih, Array.size_push]
    omega

set_option maxRecDepth 32768 in
theorem initial_eq_rows : initial = initialRows 45 0 #[] := by
  rw [Project.Drone.Initial.initial_eq]
  decide

#print axioms initial_eq_rows
end Project.Drone.Execution
