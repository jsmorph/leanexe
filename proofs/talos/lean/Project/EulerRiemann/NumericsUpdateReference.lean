import Project.EulerRiemann.NumericsUpdate

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order

theorem update_reference_error (ratio state fluxL fluxR : UInt64)
    (hr : positiveBits ratio = true) (hs : Finite state) (hl : Finite fluxL) (hh : Finite fluxR)
    (hr1 : value ratio ≤ 1) (referenceL referenceR M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (bs : |value state| ≤ M) (bl : |value fluxL| ≤ 66 * M^5) (bh : |value fluxR| ≤ 66 * M^5)
    (el : |value fluxL - referenceL| ≤ 304 * arithmeticEpsilon * M^5)
    (eh : |value fluxR - referenceR| ≤ 304 * arithmeticEpsilon * M^5) :
    let result := Project.EulerCellStep.Model.updateCheckedBits ratio state fluxL fluxR
    result.status = 0 ∧ Finite result.value ∧
    |value result.value - (value state - value ratio * (referenceR - referenceL))| ≤
      arithmeticEpsilon * M + 1004 * arithmeticEpsilon * value ratio * M^5 +
        2 * multiplicationUnderflowEpsilon := by
  obtain ⟨hstatus, hfinite, er⟩ := update_error ratio state fluxL fluxR hr hs hl hh hr1 M hM hMmax bs bl bh
  have ed : |(value fluxR - value fluxL) - (referenceR - referenceL)| ≤ 608 * arithmeticEpsilon * M^5 := by
    obtain ⟨ell, elr⟩ := abs_le.mp el
    obtain ⟨ehl, ehr⟩ := abs_le.mp eh
    apply abs_le.mpr
    constructor <;> linarith only [ell, elr, ehl, ehr]
  have hresult := Project.ProofKit.RealAffineError.subtract_product (value ratio) (value state)
    (referenceR - referenceL) (value fluxR - value fluxL)
    (value ratio * (value fluxR - value fluxL))
    (value (Project.EulerCellStep.Model.updateCheckedBits ratio state fluxL fluxR).value)
    (608 * arithmeticEpsilon * M^5) 0
    (arithmeticEpsilon * M + 396 * arithmeticEpsilon * value ratio * M^5 + 2 * multiplicationUnderflowEpsilon)
    (positiveBits_spec ratio hr).2.le ed (by simp only [sub_self, abs_zero, le_refl]) er
  exact ⟨hstatus, hfinite, hresult.trans_eq (by ring)⟩

#print axioms update_reference_error
end Project.EulerRiemann.Numerics
