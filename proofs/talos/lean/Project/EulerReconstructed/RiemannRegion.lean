import Project.EulerReconstructed.Program
import Project.EulerRiemann.Program
import Project.FunctionRegion.Exec
import Mathlib.Tactic.NormNum

namespace Project.EulerReconstructed.RiemannRegion
open Project.FunctionRegion

def rename (index : Nat) : Nat :=
  [0, 44, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 76, 138, 39, 40, 41, 42, 0, 78, 0, 79, 0, 0, 47, 48, 49, 50, 54, 55, 56, 0, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 0, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 0, 0, 0, 0, 0, 114, 115, 116, 117, 118, 119, 0, 0, 122, 123, 0, 0, 126, 127, 128, 0, 130, 131, 132, 133, 134, 135, 136, 137, 139, 140, 141, 0, 143, 144, 145, 146, 147, 0, 149, 150, 151, 152][index]!

def domain (index : Nat) : Prop :=
  index ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 30, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 70, 71, 72, 73, 74, 75, 78, 79, 82, 83, 84, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 98, 99, 100, 101, 102, 104, 105, 106, 107]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem shift :
    Shift Project.EulerRiemann.«module» Project.EulerReconstructed.«module»
      rename rename domain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  simp only [domain, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [domain]

#print axioms shift
end Project.EulerReconstructed.RiemannRegion
