import Project.EulerRiemann.NumericsInterfaceReference

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds
open Project.Euler2DConservative.Guard (decodedState)
open RealRusanov

theorem interface_reference_magnitude (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (hL : StateBounds M rhoL mxL myL energyL) (hR : StateBounds M rhoR mxR myR energyR) :
    let flux := fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR
    ∀ i, |interfaceFlux (value flux.alpha) (decodedState rhoL mxL myL energyL)
      (decodedState rhoR mxR myR energyR) i| ≤ 67 * M^5 := by
  dsimp only
  intro i
  have er := interface_reference_error rhoL mxL myL energyL rhoR mxR myR energyR M hM hMmax hL hR i
  have bw := (flux_vector_bounds rhoL mxL myL energyL rhoR mxR myR energyR M hM hMmax hL hR i).2
  rw [abs_sub_comm] at er
  have hb := magnitude_of_error _ _ _ _ er bw
  have he : 304 * arithmeticEpsilon ≤ (1 : ℝ) := by norm_num [arithmeticEpsilon]
  have heM := mul_le_mul_of_nonneg_right he (pow_nonneg (by linarith only [hM] : 0 ≤ M) 5)
  linarith only [hb, heM]

theorem reference_update_magnitude (ratio : ℝ) (hRatio : 0 ≤ ratio)
    (rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (hL : StateBounds M rhoL mxL myL energyL) (hC : StateBounds M rho mx my energy)
    (hR : StateBounds M rhoR mxR myR energyR) :
    let left := fluxCheckedBits rhoL mxL myL energyL rho mx my energy
    let right := fluxCheckedBits rho mx my energy rhoR mxR myR energyR
    ∀ i, |update ratio (value left.alpha) (value right.alpha)
      (decodedState rhoL mxL myL energyL) (decodedState rho mx my energy) (decodedState rhoR mxR myR energyR) i| ≤
      M + 134 * ratio * M^5 := by
  let left := fluxCheckedBits rhoL mxL myL energyL rho mx my energy
  let right := fluxCheckedBits rho mx my energy rhoR mxR myR energyR
  dsimp only
  intro i
  let FL := interfaceFlux (value left.alpha) (decodedState rhoL mxL myL energyL) (decodedState rho mx my energy) i
  let FR := interfaceFlux (value right.alpha) (decodedState rho mx my energy) (decodedState rhoR mxR myR energyR) i
  have hl := interface_reference_magnitude rhoL mxL myL energyL rho mx my energy M hM hMmax hL hC i
  have hr := interface_reference_magnitude rho mx my energy rhoR mxR myR energyR M hM hMmax hC hR i
  have hs := (state_words_bounds rho mx my energy M hM hC i).2
  rw [state_words_value] at hs
  have hd : |FR - FL| ≤ 134 * M^5 := by
    have ht := abs_sub FR FL
    linarith only [ht, hl, hr]
  have hi := mul_le_mul_of_nonneg_left hd hRatio
  have ht := abs_sub (decodedState rho mx my energy i) (ratio * (FR - FL))
  rw [abs_mul, abs_of_nonneg hRatio] at ht
  change |decodedState rho mx my energy i - ratio * (FR - FL)| ≤ M + 134 * ratio * M^5
  nlinarith only [ht, hi, hs]

#print axioms interface_reference_magnitude
#print axioms reference_update_magnitude
end Project.EulerRiemann.Numerics
