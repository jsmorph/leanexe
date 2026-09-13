import Project.EulerRiemann.NumericsSideBounds
import Project.EulerRiemann.NumericsComponent

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order

structure StateBounds (M : ℝ) (rho mx my energy : UInt64) : Prop where
  finiteDensity : Finite rho
  finiteMomentum : Finite mx
  finiteTransverse : Finite my
  finiteEnergy : Finite energy
  densityLower : 1 / M ≤ value rho
  densityUpper : value rho ≤ M
  momentumBound : |value mx| ≤ M
  transverseBound : |value my| ≤ M
  energyBound : |value energy| ≤ M
  internalMargin : 24 * arithmeticEpsilon * M^3 ≤
    value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
  guard : stateGuard rho mx my energy = true

theorem flux_accepted_of_bounds (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (hL : StateBounds M rhoL mxL myL energyL) (hR : StateBounds M rhoR mxR myR energyR) :
    let flux := fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR
    flux.status = 0 ∧ Finite flux.mass ∧ Finite flux.momentum ∧ Finite flux.transverse ∧ Finite flux.energy ∧
    positiveBits flux.alpha = true ∧ value flux.alpha ≤ 32 * M^2 ∧
    |value flux.mass| ≤ 66 * M^5 ∧ |value flux.momentum| ≤ 66 * M^5 ∧
    |value flux.transverse| ≤ 66 * M^5 ∧ |value flux.energy| ≤ 66 * M^5 := by
  let left := sideCheckedBits rhoL mxL myL energyL
  let right := sideCheckedBits rhoR mxR myR energyR
  let alpha := if left.speed ≤ right.speed then right.speed else left.speed
  let mass := Project.Euler2DDynamicFlux.Model.componentCheckedBits alpha left.massFlux right.massFlux rhoL rhoR
  let momentum := Project.Euler2DDynamicFlux.Model.componentCheckedBits alpha left.momentumFlux right.momentumFlux mxL mxR
  let transverse := Project.Euler2DDynamicFlux.Model.componentCheckedBits alpha left.transverseFlux right.transverseFlux myL myR
  let energy := Project.Euler2DDynamicFlux.Model.componentCheckedBits alpha left.energyFlux right.energyFlux energyL energyR
  obtain ⟨hl, hpl, bal, hfml, hfpl, hftl, hfel, bml, bpl, btl, bel⟩ :=
    side_accepted_of_bounds rhoL mxL myL energyL hL.finiteDensity hL.finiteMomentum hL.finiteTransverse
      hL.finiteEnergy M hM hMmax hL.densityLower hL.densityUpper hL.momentumBound hL.transverseBound
      hL.energyBound hL.internalMargin hL.guard
  obtain ⟨hr, hpr, bar, hfmr, hfpr, hftr, hfer, bmr, bpr, btr, ber⟩ :=
    side_accepted_of_bounds rhoR mxR myR energyR hR.finiteDensity hR.finiteMomentum hR.finiteTransverse
      hR.finiteEnergy M hM hMmax hR.densityLower hR.densityUpper hR.momentumBound hR.transverseBound
      hR.energyBound hR.internalMargin hR.guard
  have ha : positiveBits alpha = true ∧ value alpha ≤ 32 * M^2 := by
    unfold alpha
    split
    · exact ⟨hpr, bar⟩
    · exact ⟨hpl, bal⟩
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM5 : 1 ≤ M^5 := one_le_pow₀ hM
  have hM15 : M ≤ M^5 := by
    have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^4) hMpos.le
    nlinarith only [h]
  have hM35 : M^3 ≤ M^5 := by
    have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^2) (pow_nonneg hMpos.le 3)
    nlinarith only [h]
  have brl : |value rhoL| ≤ M := by
    rw [abs_of_pos (lt_of_lt_of_le (by positivity) hL.densityLower)]
    exact hL.densityUpper
  have brr : |value rhoR| ≤ M := by
    rw [abs_of_pos (lt_of_lt_of_le (by positivity) hR.densityLower)]
    exact hR.densityUpper
  obtain ⟨hms, hmf, bmass, _⟩ := component_error alpha left.massFlux right.massFlux rhoL rhoR ha.1
    hfml hfmr hL.finiteDensity hR.finiteDensity M hM hMmax ha.2
    (by linarith only [bml, hM15, hM5]) (by linarith only [bmr, hM15, hM5]) brl brr
  obtain ⟨hps, hpf, bmom, _⟩ := component_error alpha left.momentumFlux right.momentumFlux mxL mxR ha.1
    hfpl hfpr hL.finiteMomentum hR.finiteMomentum M hM hMmax ha.2
    (by linarith only [bpl, hM35, hM5]) (by linarith only [bpr, hM35, hM5]) hL.momentumBound hR.momentumBound
  obtain ⟨hts, htf, btrans, _⟩ := component_error alpha left.transverseFlux right.transverseFlux myL myR ha.1
    hftl hftr hL.finiteTransverse hR.finiteTransverse M hM hMmax ha.2
    (by linarith only [btl, hM35, hM5]) (by linarith only [btr, hM35, hM5]) hL.transverseBound hR.transverseBound
  obtain ⟨hes, hef, benergy, _⟩ := component_error alpha left.energyFlux right.energyFlux energyL energyR ha.1
    hfel hfer hL.finiteEnergy hR.finiteEnergy M hM hMmax ha.2 bel ber hL.energyBound hR.energyBound
  have hleft : (left.status == 0) = true := beq_iff_eq.mpr hl
  have hright : (right.status == 0) = true := beq_iff_eq.mpr hr
  have hcomponents : (mass.status == 0 && momentum.status == 0 && transverse.status == 0 && energy.status == 0) = true := by
    simp only [Bool.and_eq_true_iff, beq_iff_eq]
    exact ⟨⟨⟨hms, hps⟩, hts⟩, hes⟩
  have hflux : fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR =
      ⟨0, mass.value, momentum.value, transverse.value, energy.value, alpha⟩ := by
    unfold fluxCheckedBits
    rw [ite_eq_left hleft, ite_eq_left hright, ite_eq_left hcomponents]
  dsimp only
  rw [hflux]
  exact ⟨rfl, hmf, hpf, htf, hef, ha.1, ha.2, bmass, bmom, btrans, benergy⟩

#print axioms flux_accepted_of_bounds
end Project.EulerRiemann.Numerics
