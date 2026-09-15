import Project.EulerReconstructed.Program
import Project.EulerReconstruction.Program
import Project.FunctionRegion.Exec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Project.EulerReconstructed.ReconstructionRegion
open Project.FunctionRegion

def rename (index : Nat) : Nat :=
  [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 39, 40, 41, 42, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75][index]!

def domain (index : Nat) : Prop := index < 41

set_option maxRecDepth 32768 in
theorem shift :
    Shift Project.EulerReconstruction.«module» Project.EulerReconstructed.«module»
      rename rename domain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  have hi : index < 41 := hi
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [domain]

#print axioms shift
end Project.EulerReconstructed.ReconstructionRegion
