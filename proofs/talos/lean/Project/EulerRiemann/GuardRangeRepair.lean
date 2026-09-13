import Project.EulerRiemann.NumericsSafety
import Project.EulerRiemann.GuardRangeBoundary

namespace Project.EulerRiemann.GuardRangeRepair
open Project.EulerRiemann.GuardRangeBoundary

def trial (ratio : UInt64) :=
  Numerics.cellCheckedBits ratio
    density momentum 0 energy
    density momentum 0 energy
    density momentum transverse energy

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem candidate_accepted :
    Numerics.stateGuard density momentum nextTransverse.value energy = true ∧
      (Numerics.sideCheckedBits density momentum nextTransverse.value energy).status = 0 := by
  decide +kernel

theorem trial_accepted : (trial 0x3FC0000000000000).status = 0 := by
  decide +kernel

theorem smaller_trial_accepted : (trial 0x3D70000000000000).status = 0 := by
  decide +kernel

theorem conserved_values :
    (trial 0x3FC0000000000000).density = density ∧
      (trial 0x3FC0000000000000).momentum = momentum ∧
      (trial 0x3FC0000000000000).transverse = nextTransverse.value ∧
      (trial 0x3FC0000000000000).energy = energy := by
  decide +kernel

theorem trial_admissible :
    let out := trial 0x3FC0000000000000
    Project.Euler2DConservative.Guard.Admissible
      (Project.Euler2DConservative.Guard.decodedState out.density out.momentum out.transverse out.energy) :=
  (Numerics.cell_state _ _ _ _ _ _ _ _ _ _ _ _ _ trial_accepted).admissible

#print axioms candidate_accepted
#print axioms trial_accepted
#print axioms smaller_trial_accepted
#print axioms conserved_values
#print axioms trial_admissible
end Project.EulerRiemann.GuardRangeRepair
