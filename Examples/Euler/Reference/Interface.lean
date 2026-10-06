import Examples.Euler.Reference.Side
import Examples.Euler.Reference.Component
import Examples.Euler.Equations.Rusanov
import Examples.Euler.Balance

/-! The first-order solver's Rusanov interface flux against the exact Rusanov flux.  For two
states that satisfy the state bounds, `flux` accepts, its speed `alpha` is positive and at most
`32 M²`, and each of its four components is within `304 ε M⁵` of the exact flux
`Rusanov.interfaceFlux` of the two states' values with speed `alpha`, where `ε = 2⁻⁵²`. -/

namespace Examples.Euler.Reference

open Examples.Euler LeanExe.ProofKit
open CodeLib.IEEE64 (value Finite arithmeticEpsilon)
open LeanExe.ProofKit.F64ArithmeticBounds

set_option exponentiation.threshold 4096

/-- The four fluxes that `side` returns. -/
def sideComponents (s : Side) : Fin 4 → Float :=
  ![s.massFlux, s.momentumFlux, s.transverseFlux, s.energyFlux]

/-- The speed that `flux` selects: the larger of the two side speeds. -/
def interfaceSpeed (left right : Side) : Float :=
  if left.speed.toBits ≤ right.speed.toBits then right.speed else left.speed

/-- Component `i` of the interface flux that `flux` computes. -/
def interfaceComponent (rhoL mxL myL energyL rhoR mxR myR energyR : Float) (i : Fin 4) :
    Component :=
  component (interfaceSpeed (side rhoL mxL myL energyL) (side rhoR mxR myR energyR))
    (sideComponents (side rhoL mxL myL energyL) i) (sideComponents (side rhoR mxR myR energyR) i)
    (stateAt ⟨rhoL, mxL, myL, energyL⟩ i) (stateAt ⟨rhoR, mxR, myR, energyR⟩ i)

theorem real_stateAt (q : Conserved) (i : Fin 4) : real (stateAt q i) = vec q i := by
  fin_cases i <;> rfl

theorem real_sideComponents (s : Side) (i : Fin 4) :
    real (sideComponents s i) = sideFluxes s i := by
  fin_cases i <;> rfl

theorem fluxAt_mk (g : Fin 4 → Component) (s : UInt64) (a : Float) (i : Fin 4) :
    fluxAt ⟨s, (g 0).value, (g 1).value, (g 2).value, (g 3).value, a⟩ i = (g i).value := by
  fin_cases i <;> rfl

theorem sideFluxBound_le (M : ℝ) (hM : 1 ≤ M) (i : Fin 4) :
    sideFluxBound M i ≤ 48 * arithmeticEpsilon * M^5 := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM35 : M^3 ≤ M^5 := by
    have hb := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^2) (pow_nonneg hMpos.le 3)
    nlinarith only [hb]
  have he35 := mul_le_mul_of_nonneg_left hM35 epsilon_pos.le
  have he5 : 0 < arithmeticEpsilon * M^5 := mul_pos epsilon_pos (pow_pos hMpos 5)
  fin_cases i
  · show (0 : ℝ) ≤ _
    linarith only [he5]
  · show 20 * arithmeticEpsilon * M^3 ≤ _
    linarith only [he35, he5]
  · show 3 * arithmeticEpsilon * M^3 ≤ _
    linarith only [he35, he5]
  · exact le_rfl

theorem state_components_bounds (rho mx my energy : Float) (M : ℝ) (hM : 1 ≤ M)
    (h : StateBounds M rho mx my energy) (i : Fin 4) :
    Finite (stateAt ⟨rho, mx, my, energy⟩ i).toBits ∧
      |real (stateAt ⟨rho, mx, my, energy⟩ i)| ≤ M := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hr : 0 < real rho := lt_of_lt_of_le (by positivity) h.densityLower
  have br : |real rho| ≤ M := by rw [abs_of_pos hr]; exact h.densityUpper
  fin_cases i
  · exact ⟨h.finiteDensity, br⟩
  · exact ⟨h.finiteMomentum, h.momentumBound⟩
  · exact ⟨h.finiteTransverse, h.transverseBound⟩
  · exact ⟨h.finiteEnergy, h.energyBound⟩

/-- Each side flux is finite, at most `15 M⁵`, and within `48 ε M⁵` of the exact flux. -/
theorem side_vector_bounds (rho mx my energy : Float) (M : ℝ) (hM : 1 ≤ M)
    (hMmax : M ≤ (2 : ℝ)^100) (h : StateBounds M rho mx my energy) (i : Fin 4) :
    Finite (sideComponents (side rho mx my energy) i).toBits ∧
      |real (sideComponents (side rho mx my energy) i)| ≤ 15 * M^5 ∧
      |real (sideComponents (side rho mx my energy) i) -
        Equations.xFlux (vec ⟨rho, mx, my, energy⟩) i| ≤ 48 * arithmeticEpsilon * M^5 := by
  obtain ⟨_, _, _, fr, fm, ft, fe, br, bm, bt, be⟩ :=
    side_accepted_of_bounds rho mx my energy M hM hMmax h
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM15 : M ≤ M^5 := by
    have hb := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^4) hMpos.le
    nlinarith only [hb]
  have hM35 : M^3 ≤ M^5 := by
    have hb := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^2) (pow_nonneg hMpos.le 3)
    nlinarith only [hb]
  have hM5 : 0 < M^5 := pow_pos hMpos 5
  refine ⟨?_, ?_, ?_⟩
  · fin_cases i
    exacts [fr, fm, ft, fe]
  · fin_cases i
    · show |real (side rho mx my energy).massFlux| ≤ _
      linarith only [br, hM15, hM5]
    · show |real (side rho mx my energy).momentumFlux| ≤ _
      linarith only [bm, hM35, hM5]
    · show |real (side rho mx my energy).transverseFlux| ≤ _
      linarith only [bt, hM35, hM5]
    · exact be
  · rw [real_sideComponents]
    exact (side_xFlux_error rho mx my energy M hM hMmax h i).trans (sideFluxBound_le M hM i)

/-- `flux` in terms of its parts when every part accepts. -/
theorem flux_of_accepted (rhoL mxL myL energyL rhoR mxR myR energyR : Float)
    (hl : (side rhoL mxL myL energyL).status = 0) (hr : (side rhoR mxR myR energyR).status = 0)
    (h : ∀ i, (interfaceComponent rhoL mxL myL energyL rhoR mxR myR energyR i).status = 0) :
    flux rhoL mxL myL energyL rhoR mxR myR energyR =
      ⟨0, (interfaceComponent rhoL mxL myL energyL rhoR mxR myR energyR 0).value,
        (interfaceComponent rhoL mxL myL energyL rhoR mxR myR energyR 1).value,
        (interfaceComponent rhoL mxL myL energyL rhoR mxR myR energyR 2).value,
        (interfaceComponent rhoL mxL myL energyL rhoR mxR myR energyR 3).value,
        interfaceSpeed (side rhoL mxL myL energyL) (side rhoR mxR myR energyR)⟩ := by
  unfold flux
  dsimp only
  rw [ite_eq_left]
  · rfl
  · simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
    exact ⟨hl, hr, h 0, h 1, h 2, h 3⟩

/-- Under the state bounds on both states, the interface speed is positive and at most `32 M²`,
and each interface component accepts with a finite value at most `66 M⁵` that is within
`256 ε M⁵` of the Rusanov formula applied to the computed side fluxes. -/
theorem interface_component_error (rhoL mxL myL energyL rhoR mxR myR energyR : Float) (M : ℝ)
    (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100) (hL : StateBounds M rhoL mxL myL energyL)
    (hR : StateBounds M rhoR mxR myR energyR) :
    let alpha := interfaceSpeed (side rhoL mxL myL energyL) (side rhoR mxR myR energyR)
    positive alpha = true ∧ real alpha ≤ 32 * M^2 ∧ ∀ i,
      let c := interfaceComponent rhoL mxL myL energyL rhoR mxR myR energyR i
      c.status = 0 ∧ Finite c.value.toBits ∧ |real c.value| ≤ 66 * M^5 ∧
        |real c.value - ((Equations.xFlux (vec ⟨rhoL, mxL, myL, energyL⟩) i +
          Equations.xFlux (vec ⟨rhoR, mxR, myR, energyR⟩) i) / 2 -
          real alpha * (vec ⟨rhoR, mxR, myR, energyR⟩ i - vec ⟨rhoL, mxL, myL, energyL⟩ i) / 2)| ≤
          304 * arithmeticEpsilon * M^5 := by
  obtain ⟨-, hpl, bal, -⟩ := side_accepted_of_bounds rhoL mxL myL energyL M hM hMmax hL
  obtain ⟨-, hpr, bar, -⟩ := side_accepted_of_bounds rhoR mxR myR energyR M hM hMmax hR
  have ha : positive (interfaceSpeed (side rhoL mxL myL energyL) (side rhoR mxR myR energyR)) =
      true ∧ real (interfaceSpeed (side rhoL mxL myL energyL) (side rhoR mxR myR energyR)) ≤
      32 * M^2 := by
    unfold interfaceSpeed
    split
    · exact ⟨hpr, bar⟩
    · exact ⟨hpl, bal⟩
  refine ⟨ha.1, ha.2, fun i => ?_⟩
  obtain ⟨hfL, bfL, efL⟩ := side_vector_bounds rhoL mxL myL energyL M hM hMmax hL i
  obtain ⟨hfR, bfR, efR⟩ := side_vector_bounds rhoR mxR myR energyR M hM hMmax hR i
  obtain ⟨hsL, bsL⟩ := state_components_bounds rhoL mxL myL energyL M hM hL i
  obtain ⟨hsR, bsR⟩ := state_components_bounds rhoR mxR myR energyR M hM hR i
  obtain ⟨h1, h2, h3, h4⟩ := component_error _ _ _ _ _ ha.1 hfL hfR hsL hsR M hM hMmax ha.2 bfL
    bfR bsL bsR
  have h5 := RealRusanovError.reference_flux _ _ _ _ _ _ _ _ _ efL efR h4
  rw [real_stateAt, real_stateAt] at h5
  exact ⟨h1, h2, h3, h5.trans_eq (by ring)⟩

/-- Under the state bounds on both states, `flux` accepts, with a positive speed at most `32 M²`
and components at most `66 M⁵`. -/
theorem flux_accepted_of_bounds (rhoL mxL myL energyL rhoR mxR myR energyR : Float) (M : ℝ)
    (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100) (hL : StateBounds M rhoL mxL myL energyL)
    (hR : StateBounds M rhoR mxR myR energyR) :
    let f := flux rhoL mxL myL energyL rhoR mxR myR energyR
    f.status = 0 ∧ positive f.alpha = true ∧ real f.alpha ≤ 32 * M^2 ∧
      ∀ i, Finite (fluxAt f i).toBits ∧ |real (fluxAt f i)| ≤ 66 * M^5 := by
  obtain ⟨hl, -⟩ := side_accepted_of_bounds rhoL mxL myL energyL M hM hMmax hL
  obtain ⟨hr, -⟩ := side_accepted_of_bounds rhoR mxR myR energyR M hM hMmax hR
  obtain ⟨ha, ba, hc⟩ :=
    interface_component_error rhoL mxL myL energyL rhoR mxR myR energyR M hM hMmax hL hR
  rw [flux_of_accepted rhoL mxL myL energyL rhoR mxR myR energyR hl hr (fun i => (hc i).1)]
  refine ⟨rfl, ha, ba, fun i => ?_⟩
  rw [fluxAt_mk (interfaceComponent rhoL mxL myL energyL rhoR mxR myR energyR)]
  exact ⟨(hc i).2.1, (hc i).2.2.1⟩

/-- Under the state bounds on both states, each component of `flux` is within `304 ε M⁵` of the
exact Rusanov flux of the two states' values with the computed speed. -/
theorem interface_reference_error (rhoL mxL myL energyL rhoR mxR myR energyR : Float) (M : ℝ)
    (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100) (hL : StateBounds M rhoL mxL myL energyL)
    (hR : StateBounds M rhoR mxR myR energyR) (i : Fin 4) :
    let f := flux rhoL mxL myL energyL rhoR mxR myR energyR
    |real (fluxAt f i) - Equations.Rusanov.interfaceFlux (real f.alpha)
      (vec ⟨rhoL, mxL, myL, energyL⟩) (vec ⟨rhoR, mxR, myR, energyR⟩) i| ≤
      304 * arithmeticEpsilon * M^5 := by
  obtain ⟨hl, -⟩ := side_accepted_of_bounds rhoL mxL myL energyL M hM hMmax hL
  obtain ⟨hr, -⟩ := side_accepted_of_bounds rhoR mxR myR energyR M hM hMmax hR
  obtain ⟨-, -, hc⟩ :=
    interface_component_error rhoL mxL myL energyL rhoR mxR myR energyR M hM hMmax hL hR
  rw [flux_of_accepted rhoL mxL myL energyL rhoR mxR myR energyR hl hr (fun i => (hc i).1)]
  dsimp only
  rw [fluxAt_mk (interfaceComponent rhoL mxL myL energyL rhoR mxR myR energyR)]
  exact (hc i).2.2.2

end Examples.Euler.Reference
