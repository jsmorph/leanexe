import Project.EulerReconstructed.FrozenProgram
import Project.EulerOutwardFaceStep.Program
import Project.FunctionRegion.Exec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Project.EulerReconstructed.Frozen.FaceRegion
open Project.FunctionRegion

def rename (index : Nat) : Nat :=
  [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 3, 27, 28, 29, 1, 30, 2, 31, 32, 33, 34, 35, 36, 37, 38, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 39, 40, 41, 42, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105][index]!

def domain (index : Nat) : Prop := index < 71

set_option maxRecDepth 32768

private def FunctionMatches (index : Nat) : Prop :=
  ∃ f,
    Project.EulerOutwardFaceStep.«module».funcs[index]? = some f ∧
    Project.EulerReconstructed.Frozen.«module».funcs[rename index]? =
      some (renameFunction rename rename f) ∧
    PortableProgram domain f.body

private theorem functions_first (index : Nat) (hi : index < 24) :
    FunctionMatches index := by
  unfold FunctionMatches
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [domain]

private theorem functions_middle (index : Nat) (lo : 24 ≤ index) (hi : index < 48) :
    FunctionMatches index := by
  unfold FunctionMatches
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [domain]

private theorem functions_last (index : Nat) (lo : 48 ≤ index) (hi : index < 71) :
    FunctionMatches index := by
  unfold FunctionMatches
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [domain]

theorem shift :
    Shift Project.EulerOutwardFaceStep.«module» Project.EulerReconstructed.Frozen.«module»
      rename rename domain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  by_cases first : index < 24
  · exact functions_first index first
  by_cases middle : index < 48
  · exact functions_middle index (by omega) middle
  exact functions_last index (by omega) hi

#print axioms shift
end Project.EulerReconstructed.Frozen.FaceRegion
