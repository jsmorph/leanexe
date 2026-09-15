import Project.EulerReconstructed.Program
import Project.EulerOutwardGrid.Program
import Project.FunctionRegion.Exec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Project.EulerReconstructed.GridRegion
open Project.FunctionRegion

def rename (index : Nat) : Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46][index]!

def domain (index : Nat) : Prop := index < 45

set_option maxRecDepth 32768 in
theorem shift :
    Shift Project.EulerOutwardGrid.«module» Project.EulerReconstructed.«module»
      rename rename domain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  have hi : index < 45 := hi
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [domain]

#print axioms shift
end Project.EulerReconstructed.GridRegion
