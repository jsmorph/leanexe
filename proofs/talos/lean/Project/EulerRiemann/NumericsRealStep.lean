import Project.EulerRiemann.NumericsFluxWave
import Project.EulerRiemann.NumericsCfl
import Project.EulerRiemann.RealCflStep
import Project.EulerRiemann.RealStepHalfSound

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.ProofKit.F64ArithmeticBounds
open Project.Euler2DConservative.Guard (Vec4 decodedState internalEnergy pressure)
open RealRusanov

theorem bounded_state_positive (rho mx my energy : UInt64) (M : ℝ) (hM : 1 ≤ M)
    (h : StateBounds M rho mx my energy) :
    let q := decodedState rho mx my energy
    0 < q 0 ∧ 0 < internalEnergy q := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hr : 0 < value rho := lt_of_lt_of_le (by positivity) h.densityLower
  have heM := mul_pos epsilon_pos (pow_pos hMpos 3)
  have hm := h.internalMargin
  refine ⟨hr, ?_⟩
  change 0 < value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
  linarith only [hm, heM]

private theorem sound_properties (q : Vec4) (hr : 0 < q 0) (hi : 0 < internalEnergy q) :
    let c := Real.sqrt ((14 / 25) * (internalEnergy q / q 0))
    0 < c ∧ c^2 = (7 / 5) * pressure q / q 0 := by
  have hrad : 0 < (14 / 25 : ℝ) * (internalEnergy q / q 0) := by positivity
  refine ⟨Real.sqrt_pos.mpr hrad, ?_⟩
  rw [Real.sq_sqrt hrad.le]
  simp only [pressure]
  ring

theorem reference_step_positive (ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (hr : positiveBits ratio = true) (br : value ratio ≤ 1)
    (hL : StateBounds M rhoL mxL myL energyL) (hC : StateBounds M rho mx my energy)
    (hR : StateBounds M rhoR mxR myR energyR) :
    let left := fluxCheckedBits rhoL mxL myL energyL rho mx my energy
    let right := fluxCheckedBits rho mx my energy rhoR mxR myR energyR
    let alpha := if left.alpha ≤ right.alpha then right.alpha else left.alpha
    let courant := Wasm.IEEE64.mul ratio alpha
    positiveBits courant = true → courant ≤ 0x3FE0000000000000 →
    let qL := decodedState rhoL mxL myL energyL
    let qC := decodedState rho mx my energy
    let qR := decodedState rhoR mxR myR energyR
    let result := update (value ratio) (value left.alpha) (value right.alpha) qL qC qR
    (49 / 100) * qC 0 ≤ result 0 ∧
      (49 / 100) * internalEnergy qC ≤ internalEnergy result ∧
      0 < result 0 ∧ 0 < internalEnergy result := by
  dsimp only
  intro hc hhalf
  let left := fluxCheckedBits rhoL mxL myL energyL rho mx my energy
  let right := fluxCheckedBits rho mx my energy rhoR mxR myR energyR
  let qL := decodedState rhoL mxL myL energyL
  let qC := decodedState rho mx my energy
  let qR := decodedState rhoR mxR myR energyR
  let cL := Real.sqrt ((14 / 25) * (internalEnergy qL / qL 0))
  let cR := Real.sqrt ((14 / 25) * (internalEnergy qR / qR 0))
  obtain ⟨_, _, _, _, _, hla, bla, _⟩ := flux_accepted_of_bounds rhoL mxL myL energyL
    rho mx my energy M hM hMmax hL hC
  obtain ⟨_, _, _, _, _, hra, bra, _⟩ := flux_accepted_of_bounds rho mx my energy
    rhoR mxR myR energyR M hM hMmax hC hR
  have hCfl := selected_courant_bound ratio left.alpha right.alpha hr hla hra M hM hMmax br bla bra hc hhalf
  have hRatio := (positiveBits_spec ratio hr).2
  have hLeft := (positiveBits_spec left.alpha hla).2
  have hRight := (positiveBits_spec right.alpha hra).2
  have hLState := bounded_state_positive rhoL mxL myL energyL M hM hL
  have hCState := bounded_state_positive rho mx my energy M hM hC
  have hRState := bounded_state_positive rhoR mxR myR energyR M hM hR
  have hLSound := sound_properties qL hLState.1 hLState.2
  have hRSound := sound_properties qR hRState.1 hRState.2
  have hLWave : |qL 1 / qL 0| + cL / 2 ≤ value left.alpha :=
    (flux_speed_lower rhoL mxL myL energyL rho mx my energy M hM hMmax hL hC).1
  have hRWave : |qR 1 / qR 0| + cR / 2 ≤ value right.alpha :=
    (flux_speed_lower rho mx my energy rhoR mxR myR energyR M hM hMmax hC hR).2
  have hWave (u c a : ℝ) (ha : 0 < a) (h : |u| + c / 2 ≤ a) :
      |1 / a| * (|u| + c / 2) ≤ 1 := by
    rw [abs_of_pos (by positivity : 0 < 1 / a), one_div, inv_mul_eq_div]
    exact (div_le_one ha).mpr h
  have hl := split_half_sound_positive qL (1 / value left.alpha) cL hLState.1 hLState.2
    hLSound.1 hLSound.2 (hWave _ _ _ hLeft hLWave)
  have ht := split_half_sound_positive qR (-1 / value right.alpha) cR hRState.1 hRState.2
    hRSound.1 hRSound.2 (by
      simpa only [neg_div, abs_neg] using hWave _ _ _ hRight hRWave)
  exact update_positive_weight (value ratio) (value left.alpha) (value right.alpha) (49 / 100)
    qL qC qR hRatio.le hLeft hRight (by norm_num) (by linarith only [hCfl]) hCState hl ht

#print axioms bounded_state_positive
#print axioms reference_step_positive
end Project.EulerRiemann.Numerics
