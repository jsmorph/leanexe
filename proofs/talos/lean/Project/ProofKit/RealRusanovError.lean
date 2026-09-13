import Mathlib.Tactic

namespace Project.ProofKit.RealRusanovError

theorem reference_flux (fluxL fluxR referenceL referenceR viscosity result errorLeft errorRight errorResult : ℝ)
    (hl : |fluxL - referenceL| ≤ errorLeft) (hr : |fluxR - referenceR| ≤ errorRight)
    (he : |result - ((fluxL + fluxR) / 2 - viscosity)| ≤ errorResult) :
    |result - ((referenceL + referenceR) / 2 - viscosity)| ≤
      errorResult + (errorLeft + errorRight) / 2 := by
  obtain ⟨hll, hlr⟩ := abs_le.mp hl
  obtain ⟨hrl, hrr⟩ := abs_le.mp hr
  obtain ⟨hel, her⟩ := abs_le.mp he
  apply abs_le.mpr
  constructor <;> linarith only [hll, hlr, hrl, hrr, hel, her]

theorem component (alpha fluxL fluxR stateL stateR sum mean jump viscosity halfViscosity result
    es em ej ev eh er : ℝ) (ha : 0 ≤ alpha)
    (hs : |sum - (fluxL + fluxR)| ≤ es) (hm : |mean - sum / 2| ≤ em)
    (hj : |jump - (stateR - stateL)| ≤ ej)
    (hv : |viscosity - alpha * jump| ≤ ev) (hh : |halfViscosity - viscosity / 2| ≤ eh)
    (hr : |result - (mean - halfViscosity)| ≤ er) :
    |result - ((fluxL + fluxR) / 2 - alpha * (stateR - stateL) / 2)| ≤
      es / 2 + em + alpha * ej / 2 + ev / 2 + eh + er := by
  have hs' := abs_le.mp hs
  have hm' := abs_le.mp hm
  have hj' := abs_le.mp hj
  have hv' := abs_le.mp hv
  have hh' := abs_le.mp hh
  have hr' := abs_le.mp hr
  have hjlo := mul_le_mul_of_nonneg_left hj'.1 ha
  have hjhi := mul_le_mul_of_nonneg_left hj'.2 ha
  apply abs_le.mpr
  constructor <;> linarith only [hs'.1, hs'.2, hm'.1, hm'.2, hjlo, hjhi,
    hv'.1, hv'.2, hh'.1, hh'.2, hr'.1, hr'.2]

#print axioms reference_flux
#print axioms component
end Project.ProofKit.RealRusanovError
