import Project.EulerReconstructed.Program
import Project.EulerOutwardFaceStep.Program
import Project.FunctionRegion.Exec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Project.EulerReconstructed.FaceRegion
open Project.FunctionRegion

def rename (index : Nat) : Nat :=
  [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 3, 27, 28, 29, 1, 30, 2, 31, 32, 33, 34, 35, 36, 37, 38, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 39, 40, 41, 42, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105][index]!

def domain (index : Nat) : Prop := index < 71

set_option maxRecDepth 32768 in
theorem shift :
    Shift Project.EulerOutwardFaceStep.«module» Project.EulerReconstructed.«module»
      rename rename domain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  have hi : index < 71 := hi
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [domain]

#print axioms shift
end Project.EulerReconstructed.FaceRegion
