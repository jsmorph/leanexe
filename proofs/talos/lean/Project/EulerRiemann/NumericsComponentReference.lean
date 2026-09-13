import Project.EulerRiemann.NumericsComponent

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order

theorem component_reference_error (alpha fluxL fluxR stateL stateR : UInt64)
    (ha : positiveBits alpha = true) (hfL : Finite fluxL) (hfR : Finite fluxR)
    (hsL : Finite stateL) (hsR : Finite stateR)
    (referenceL referenceR M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (ba : value alpha ≤ 32 * M^2) (bfL : |value fluxL| ≤ 15 * M^5) (bfR : |value fluxR| ≤ 15 * M^5)
    (bsL : |value stateL| ≤ M) (bsR : |value stateR| ≤ M)
    (efL : |value fluxL - referenceL| ≤ 48 * arithmeticEpsilon * M^5)
    (efR : |value fluxR - referenceR| ≤ 48 * arithmeticEpsilon * M^5) :
    let result := Project.EulerDynamicFlux.Model.componentCheckedBits alpha fluxL fluxR stateL stateR
    |value result.value - ((referenceL + referenceR) / 2 -
      value alpha * (value stateR - value stateL) / 2)| ≤ 304 * arithmeticEpsilon * M^5 := by
  obtain ⟨_, _, _, er⟩ := component_error alpha fluxL fluxR stateL stateR
    ha hfL hfR hsL hsR M hM hMmax ba bfL bfR bsL bsR
  have h := Project.ProofKit.RealRusanovError.reference_flux (value fluxL) (value fluxR)
    referenceL referenceR (value alpha * (value stateR - value stateL) / 2)
    (value (Project.EulerDynamicFlux.Model.componentCheckedBits alpha fluxL fluxR stateL stateR).value)
    (48 * arithmeticEpsilon * M^5) (48 * arithmeticEpsilon * M^5) (256 * arithmeticEpsilon * M^5)
    efL efR er
  exact h.trans_eq (by ring)

#print axioms component_reference_error
end Project.EulerRiemann.Numerics
