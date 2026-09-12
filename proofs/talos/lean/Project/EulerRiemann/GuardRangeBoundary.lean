import Project.Euler2DCellStep.Model
import Project.Euler2DConservative.Guard

namespace Project.EulerRiemann.GuardRangeBoundary
open CodeLib.IEEE64 (value)
open Project.Euler2DConservative.Model
open Project.Euler2DCellStep.Model (cellCheckedBits)

open Project.Euler2DDynamicFlux.Model (fluxCheckedBits)
open Project.EulerCellStep.Model (updateCheckedBits)

def density : UInt64 := 0x3FF0000000000000
def momentum : UInt64 := 0x3FF4000000000000
def energy : UInt64 := 0x4000000000000000
def transverse : UInt64 := 0x0040000000000000

def trial (ratio : UInt64) :=
  cellCheckedBits ratio
    density momentum 0 energy
    density momentum 0 energy
    density momentum transverse energy

def leftFlux := fluxCheckedBits density momentum 0 energy density momentum 0 energy
def rightFlux := fluxCheckedBits density momentum 0 energy density momentum transverse energy
def nextTransverse := updateCheckedBits 0x3FC0000000000000 0
  leftFlux.transverse rightFlux.transverse

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem inputs_accepted :
    (sideCheckedBits density momentum 0 energy).status = 0 ∧
      (sideCheckedBits density momentum transverse energy).status = 0 := by
  decide +kernel

theorem trial_rejected : (trial 0x3FC0000000000000).status = 1 := by
  decide +kernel

theorem smaller_trial_rejected : (trial 0x3D70000000000000).status = 1 := by
  decide +kernel

theorem normalizable_range_boundary :
    normalizable transverse (topExponent density momentum transverse energy) = true ∧
      normalizable 0x0030000000000000
        (topExponent density momentum 0x0030000000000000 energy) = false := by
  decide +kernel

theorem trial_intermediates :
    leftFlux.status = 0 ∧ rightFlux.status = 0 ∧ leftFlux.alpha = rightFlux.alpha ∧
      positiveBits (Wasm.IEEE64.mul 0x3FC0000000000000 rightFlux.alpha) = true ∧
      Wasm.IEEE64.mul 0x3FC0000000000000 rightFlux.alpha ≤ 0x3FE0000000000000 ∧
      updateCheckedBits 0x3FC0000000000000 density leftFlux.mass rightFlux.mass = ⟨0, density⟩ ∧
      updateCheckedBits 0x3FC0000000000000 momentum leftFlux.momentum rightFlux.momentum = ⟨0, momentum⟩ ∧
      updateCheckedBits 0x3FC0000000000000 energy leftFlux.energy rightFlux.energy = ⟨0, energy⟩ ∧
      nextTransverse.status = 0 := by
  decide +kernel

theorem transverse_range_rejection :
    positiveBits nextTransverse.value = true ∧
      nextTransverse.value ≤ 0x3FE0000000000000 ∧
      normalizable nextTransverse.value
        (topExponent density momentum nextTransverse.value energy) = false ∧
      stateGuard density momentum nextTransverse.value energy = false := by
  decide +kernel

set_option exponentiation.threshold 4096 in
theorem rejected_candidate_admissible :
    Project.Euler2DConservative.Guard.Admissible
      (Project.Euler2DConservative.Guard.decodedState
        density momentum nextTransverse.value energy) := by
  have hd : value density = 1 := by
    change ((2^1074 : Nat) : ℝ) / (2 : ℝ)^1074 = 1
    norm_num
  have hm : value momentum = 5 / 4 := by
    change ((5 * 2^1072 : Nat) : ℝ) / (2 : ℝ)^1074 = 5 / 4
    norm_num
  have he : CodeLib.IEEE64.value energy = 2 := by
    change ((2^1075 : Nat) : ℝ) / (2 : ℝ)^1074 = 2
    norm_num
  have hh : CodeLib.IEEE64.value 0x3FE0000000000000 = 1 / 2 := by
    change ((2^1073 : Nat) : ℝ) / (2 : ℝ)^1074 = 1 / 2
    norm_num
  have hp := transverse_range_rejection.1
  have ht := Project.ProofKit.F64Order.abs_value_mono nextTransverse.value
    0x3FE0000000000000 (by
      rw [Project.ProofKit.F64Order.absBits_of_positive _ hp,
        Project.ProofKit.F64Order.absBits_of_positive _ (by decide)]
      exact transverse_range_rejection.2.1)
  rw [hh] at ht
  norm_num at ht
  have hs : (CodeLib.IEEE64.value nextTransverse.value)^2 ≤ (1 / 2 : ℝ)^2 := by
    exact (sq_le_sq₀ (Project.ProofKit.F64Order.positiveBits_spec _ hp).2.le
      (by norm_num)).mpr (le_of_abs_le ht)
  change 0 < value density ∧
    0 < (2 / 5 : ℝ) * (value energy -
      ((value momentum)^2 + (value nextTransverse.value)^2) / (2 * value density))
  rw [hd, hm, he]
  constructor <;> nlinarith

#print axioms inputs_accepted
#print axioms trial_rejected
#print axioms smaller_trial_rejected
#print axioms normalizable_range_boundary
#print axioms trial_intermediates
#print axioms transverse_range_rejection
#print axioms rejected_candidate_admissible
end Project.EulerRiemann.GuardRangeBoundary
