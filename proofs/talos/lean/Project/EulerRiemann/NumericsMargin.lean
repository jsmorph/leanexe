import Project.EulerRiemann.Numerics
import Project.EulerRiemann.RealPerturbation
import Project.ProofKit.F64AdmissibilityRange

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.Euler2DConservative.Guard (Vec4 decodedState)
open Project.EulerRiemann.RealRusanov
open Project.ProofKit.F64Order
open Project.ProofKit.F64Admissibility (topExponent normalizable)
open Project.ProofKit.F64AdmissibilityTiny (exactResidual)

noncomputable def guardMarginBudget (rho mx my energy : UInt64) : ℝ :=
  26 * arithmeticEpsilon * ((2 : ℝ)^(topExponent rho mx my energy).toNat)^2 /
    ((2 : ℝ)^1021)^2

theorem exactResidual_above_threshold (rho mx my energy : UInt64)
    (hr : 0 < value rho) (he : 0 < value energy)
    (hm : guardMarginBudget rho mx my energy < energyMargin (decodedState rho mx my energy)) :
    13 * arithmeticEpsilon < exactResidual rho mx my energy := by
  have hs := Project.ProofKit.F64AdmissibilityTiny.exactResidual_scaled
    rho mx my energy hr he
  have ha : 0 < ((2 : ℝ)^1021)^2 := by positivity
  have hb : 0 < ((2 : ℝ)^(topExponent rho mx my energy).toNat)^2 := by positivity
  have hm' := (div_lt_iff₀ ha).mp hm
  change 26 * arithmeticEpsilon * ((2 : ℝ)^(topExponent rho mx my energy).toNat)^2 <
    (2 * value rho * value energy - (value mx)^2 - (value my)^2) * ((2 : ℝ)^1021)^2 at hm'
  by_contra h
  have hle := mul_le_mul_of_nonneg_right (le_of_not_gt h) hb.le
  nlinarith only [hs, hm', hle]

theorem stateGuard_of_perturbation (rho mx my energy : UInt64)
    (reference : Vec4) (bound error : ℝ)
    (hr : Finite rho) (hx : Finite mx) (hy : Finite my) (he : Finite energy)
    (ht : 1021 ≤ topExponent rho mx my energy)
    (nr : normalizable rho (topExponent rho mx my energy) = true)
    (ne : normalizable energy (topExponent rho mx my energy) = true)
    (hq : ∀ i, |reference i| ≤ bound)
    (hError : ∀ i, |decodedState rho mx my energy i - reference i| ≤ error)
    (hDensity : error < reference 0)
    (hMargin : 8 * bound * error + 4 * error^2 + guardMarginBudget rho mx my energy <
      energyMargin reference) :
    stateGuard rho mx my energy = true := by
  have hBudget : 0 ≤ guardMarginBudget rho mx my energy := by
    unfold guardMarginBudget arithmeticEpsilon
    positivity
  have hAdmissible := admissible_of_perturbation reference (decodedState rho mx my energy)
    bound error hq hError hDensity (by linarith)
  have hRho : 0 < value rho := hAdmissible.1
  have hChange := (abs_le.mp
    (energyMargin_perturbation reference (decodedState rho mx my energy)
      bound error hq hError)).1
  have hMarginNext : guardMarginBudget rho mx my energy <
      energyMargin (decodedState rho mx my energy) := by linarith
  have hPositive := hBudget.trans_lt hMarginNext
  change 0 < 2 * value rho * value energy - (value mx)^2 - (value my)^2 at hPositive
  have hEnergy : 0 < value energy := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos hRho.le (le_of_not_gt hn)
    nlinarith only [hp, hPositive, sq_nonneg (value mx), sq_nonneg (value my)]
  apply Bool.or_eq_true_iff.mpr
  right
  exact Project.ProofKit.F64AdmissibilityTiny.checked_of_margin_and_top
    rho mx my energy (positiveBits_of_finite_value_pos rho hr hRho)
    ((finiteBits_iff mx).mpr hx) ((finiteBits_iff my).mpr hy)
    (positiveBits_of_finite_value_pos energy he hEnergy) ht nr ne
    (exactResidual_above_threshold rho mx my energy hRho hEnergy hMarginNext)

#print axioms exactResidual_above_threshold
#print axioms stateGuard_of_perturbation
end Project.EulerRiemann.Numerics
