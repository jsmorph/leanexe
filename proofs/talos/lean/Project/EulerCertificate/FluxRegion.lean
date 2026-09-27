import Project.EulerCertificate.Program
import Project.EulerCertificateFlux.Program
import Project.FunctionRegion.Exec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Project.EulerCertificate.FluxRegion
open Project.FunctionRegion

def rename (index : Nat) : Nat :=
  [8, 55, 56, 57, 58, 32, 33, 59, 60, 61, 62, 63, 68, 10, 11, 69, 78, 164, 71, 23, 24, 31, 64, 65, 0, 80, 165, 25, 166, 167, 168, 9, 12, 13, 14, 169, 191, 192, 193, 194][index]!

def domain (index : Nat) : Prop :=
  index < 35 ∨ (36 ≤ index ∧ index < 40)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem shift :
    Shift Project.EulerCertificateFlux.«module» Project.EulerCertificate.«module»
      rename rename domain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  rcases hi with hi | ⟨hlo, hhi⟩
  all_goals try interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [domain]

#print axioms shift
end Project.EulerCertificate.FluxRegion

