import Project.EulerRiemann.NumericsComponentResidual

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64RusanovResidual
open Project.EulerDynamicFlux.Model (componentCheckedBits)
set_option exponentiation.threshold 4096

theorem accepted_component_reference_bound (alpha fluxL fluxR stateL stateR : UInt64)
    (FL FR leftError rightError : ℝ)
    (h : (componentCheckedBits alpha fluxL fluxR stateL stateR).status = 0)
    (hL : |value fluxL - FL| ≤ leftError) (hR : |value fluxR - FR| ≤ rightError) :
    let output := (componentCheckedBits alpha fluxL fluxR stateL stateR).value
    |value output - (1 / 2) * (FL + FR - value alpha * (value stateR - value stateL))| ≤
      errorBound 0x3FE0000000000000 alpha fluxL fluxR stateL stateR output +
        (1 / 2) * (leftError + rightError) := by
  have halfValue : value 0x3FE0000000000000 = 1 / 2 := by
    change ((2^1073 : Nat) : ℝ) / (2 : ℝ)^1074 = 1 / 2
    norm_num
  have hc := accepted_component_residual_bound alpha fluxL fluxR stateL stateR h
  unfold Project.ProofKit.F64RusanovResidual.residual at hc
  rw [halfValue] at hc
  have hsum : |(value fluxL - FL) + (value fluxR - FR)| ≤ leftError + rightError :=
    (abs_add_le _ _).trans (add_le_add hL hR)
  have hweighted : |(1 / 2 : ℝ) * ((value fluxL - FL) + (value fluxR - FR))| ≤
      (1 / 2) * (leftError + rightError) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hid : (1 / 2 : ℝ) *
      (value fluxL + value fluxR - value alpha * (value stateR - value stateL)) -
      (1 / 2) * (FL + FR - value alpha * (value stateR - value stateL)) =
      (1 / 2) * ((value fluxL - FL) + (value fluxR - FR)) := by ring
  calc
    _ ≤ |value (componentCheckedBits alpha fluxL fluxR stateL stateR).value -
        (1 / 2) * (value fluxL + value fluxR - value alpha * (value stateR - value stateL))| +
        |(1 / 2) * (value fluxL + value fluxR - value alpha * (value stateR - value stateL)) -
          (1 / 2) * (FL + FR - value alpha * (value stateR - value stateL))| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hc (by rw [hid]; exact hweighted)

#print axioms accepted_component_reference_bound
end Project.EulerRiemann.Numerics
