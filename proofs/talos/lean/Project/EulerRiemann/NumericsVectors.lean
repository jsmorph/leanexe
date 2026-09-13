import Project.EulerRiemann.NumericsFluxReference
import Project.EulerRiemann.RealRusanov

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds
open Project.Euler2DConservative.Guard (decodedState internalEnergy pressure)
open RealRusanov

def stateWords (rho mx my energy : UInt64) : Fin 4 → UInt64 := ![rho, mx, my, energy]

def sideFluxWords (side : Project.Euler2DConservative.Model.CheckedSideBits) : Fin 4 → UInt64 :=
  ![side.massFlux, side.momentumFlux, side.transverseFlux, side.energyFlux]

def fluxWords (flux : Project.Euler2DDynamicFlux.Model.CheckedFlux) : Fin 4 → UInt64 :=
  ![flux.mass, flux.momentum, flux.transverse, flux.energy]

theorem state_words_value (rho mx my energy : UInt64) (i : Fin 4) :
    value (stateWords rho mx my energy i) = decodedState rho mx my energy i := by
  fin_cases i <;> rfl

theorem state_words_bounds (rho mx my energy : UInt64) (M : ℝ) (hM : 1 ≤ M)
    (h : StateBounds M rho mx my energy) (i : Fin 4) :
    Finite (stateWords rho mx my energy i) ∧ |value (stateWords rho mx my energy i)| ≤ M := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hr : 0 < value rho := lt_of_lt_of_le (by positivity) h.densityLower
  have br : |value rho| ≤ M := by rw [abs_of_pos hr]; exact h.densityUpper
  fin_cases i
  · exact ⟨h.finiteDensity, br⟩
  · exact ⟨h.finiteMomentum, h.momentumBound⟩
  · exact ⟨h.finiteTransverse, h.transverseBound⟩
  · exact ⟨h.finiteEnergy, h.energyBound⟩

theorem side_vector_bounds (rho mx my energy : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100) (h : StateBounds M rho mx my energy) :
    let side := sideCheckedBits rho mx my energy
    let q := decodedState rho mx my energy
    ∀ i, Finite (sideFluxWords side i) ∧ |value (sideFluxWords side i)| ≤ 15 * M^5 ∧
      |value (sideFluxWords side i) - physicalFlux q i| ≤ 48 * arithmeticEpsilon * M^5 := by
  let side := sideCheckedBits rho mx my energy
  obtain ⟨_, _, _, fr, fm, ft, fe, br, bm, bt, be⟩ := side_accepted_of_bounds rho mx my energy
    h.finiteDensity h.finiteMomentum h.finiteTransverse h.finiteEnergy M hM hMmax
    h.densityLower h.densityUpper h.momentumBound h.transverseBound h.energyBound h.internalMargin h.guard
  obtain ⟨er, em, et, ee⟩ := side_flux_reference_error rho mx my energy M hM hMmax h
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM5 : 0 < M^5 := pow_pos hMpos 5
  have hM15 : M ≤ M^5 := by
    have hb := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^4) hMpos.le
    nlinarith only [hb]
  have hM35 : M^3 ≤ M^5 := by
    have hb := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^2) (pow_nonneg hMpos.le 3)
    nlinarith only [hb]
  have he35 := mul_le_mul_of_nonneg_left hM35 epsilon_pos.le
  have he5 : 0 < arithmeticEpsilon * M^5 := mul_pos epsilon_pos hM5
  dsimp only
  intro i
  fin_cases i
  · change Finite side.massFlux ∧ |value side.massFlux| ≤ 15 * M^5 ∧
      |value side.massFlux - value mx| ≤ 48 * arithmeticEpsilon * M^5
    refine ⟨fr, by linarith only [br, hM15, hM5], ?_⟩
    rw [er, sub_self, abs_zero]
    linarith only [he5]
  · refine ⟨fm, ?_, ?_⟩
    · change |value side.momentumFlux| ≤ 15 * M^5
      linarith only [bm, hM35, hM5]
    · change |value side.momentumFlux - ((value mx)^2 / value rho +
        (2 / 5) * (value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)))| ≤
        48 * arithmeticEpsilon * M^5
      linarith only [em, he35, he5]
  · refine ⟨ft, ?_, ?_⟩
    · change |value side.transverseFlux| ≤ 15 * M^5
      linarith only [bt, hM35, hM5]
    · change |value side.transverseFlux - value mx * value my / value rho| ≤ 48 * arithmeticEpsilon * M^5
      linarith only [et, he35, he5]
  · exact ⟨fe, be, ee⟩

theorem flux_vector_bounds (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (hL : StateBounds M rhoL mxL myL energyL) (hR : StateBounds M rhoR mxR myR energyR) :
    let flux := fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR
    ∀ i, Finite (fluxWords flux i) ∧ |value (fluxWords flux i)| ≤ 66 * M^5 := by
  obtain ⟨_, fr, fm, ft, fe, _, _, br, bm, bt, be⟩ :=
    flux_accepted_of_bounds rhoL mxL myL energyL rhoR mxR myR energyR M hM hMmax hL hR
  dsimp only
  intro i
  fin_cases i
  · exact ⟨fr, br⟩
  · exact ⟨fm, bm⟩
  · exact ⟨ft, bt⟩
  · exact ⟨fe, be⟩

#print axioms state_words_value
#print axioms state_words_bounds
#print axioms side_vector_bounds
#print axioms flux_vector_bounds
end Project.EulerRiemann.Numerics
