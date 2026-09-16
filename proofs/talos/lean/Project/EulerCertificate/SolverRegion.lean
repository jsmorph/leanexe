import Project.EulerCertificate.Program
import Project.EulerReconstructed.Program
import Project.FunctionRegion.Exec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Project.EulerCertificate.SolverRegion
open Project.FunctionRegion

def rename (index : Nat) : Nat :=
  [76, 55, 56, 62, 77, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 59, 60, 61, 63, 64, 78, 68, 79, 80, 81, 82, 83, 84, 85, 86, 0, 23, 24, 25, 87, 1, 88, 89, 54, 90, 91, 92, 93, 94, 95, 96, 51, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 46, 117, 49, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 48, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 0, 0, 0, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 26, 47, 50, 52, 53, 0, 2, 3, 0, 0, 0, 0, 191, 192, 193, 194][index]!

def domain (index : Nat) : Prop :=
  index < 124 ∨ (130 ≤ index ∧ index ≤ 141) ∨ index = 143 ∨ index = 144 ∨ (149 ≤ index ∧ index < 153)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem shift :
    Shift Project.EulerReconstructed.«module» Project.EulerCertificate.«module»
      rename rename domain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  rcases hi with hi | ⟨hlo, hhi⟩ | rfl | rfl | ⟨hlo, hhi⟩
  all_goals try interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [domain]

#print axioms shift
end Project.EulerCertificate.SolverRegion

