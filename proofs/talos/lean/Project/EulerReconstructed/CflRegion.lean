import Project.EulerReconstructed.Program
import Project.EulerOutwardCfl.Program
import Project.FunctionRegion.Exec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Project.EulerReconstructed.CflRegion
open Project.FunctionRegion

def rename (index : Nat) : Nat :=
  [10, 11, 24, 25, 26, 3, 27, 28, 47, 51, 1, 9, 29, 2, 52, 53][index]!

def domain (index : Nat) : Prop := index < 16

set_option maxRecDepth 32768 in
theorem shift :
    Shift Project.EulerOutwardCfl.«module» Project.EulerReconstructed.«module»
      rename rename domain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  have hi : index < 16 := hi
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [domain]

#print axioms shift
end Project.EulerReconstructed.CflRegion
