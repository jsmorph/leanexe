import Project.EulerRiemann.NumericsCandidateBounds
import Project.EulerRiemann.NumericsMargin

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.ProofKit.F64Admissibility (topExponent normalizable)
open Project.Euler2DConservative.Guard (Vec4 decodedState)
open RealRusanov

theorem candidate_guard_sufficient (ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (hr : positiveBits ratio = true) (br : value ratio ≤ 1)
    (hL : StateBounds M rhoL mxL myL energyL) (hC : StateBounds M rho mx my energy)
    (hR : StateBounds M rhoR mxR myR energyR) :
    let left := fluxCheckedBits rhoL mxL myL energyL rho mx my energy
    let right := fluxCheckedBits rho mx my energy rhoR mxR myR energyR
    let alpha := if left.alpha ≤ right.alpha then right.alpha else left.alpha
    let courant := Wasm.IEEE64.mul ratio alpha
    positiveBits courant = true → courant ≤ 0x3FE0000000000000 →
    let words := candidateWords ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR
    let top := topExponent (words 0) (words 1) (words 2) (words 3)
    let weight := 1 - value ratio * (value left.alpha + value right.alpha) / 2
    let bound := M + 134 * value ratio * M^5
    let error := arithmeticEpsilon * M + 1004 * arithmeticEpsilon * value ratio * M^5 +
      2 * multiplicationUnderflowEpsilon
    1021 ≤ top → normalizable (words 0) top = true → normalizable (words 3) top = true →
    error < weight * value rho →
    8 * bound * error + 4 * error^2 + guardMarginBudget (words 0) (words 1) (words 2) (words 3) <
      weight^2 * energyMargin (decodedState rho mx my energy) →
    stateGuard (words 0) (words 1) (words 2) (words 3) = true := by
  dsimp only
  intro hc hhalf ht nr ne hDensity hMargin
  let words := candidateWords ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR
  obtain ⟨hFinite, _, hd, hm⟩ := candidate_margin_bounds ratio rhoL mxL myL energyL rho mx my energy
    rhoR mxR myR energyR M hM hMmax hr br hL hC hR hc hhalf
  have hState : decodedState (words 0) (words 1) (words 2) (words 3) = (fun i => value (words i) : Vec4) := by
    funext i
    fin_cases i <;> rfl
  have hRho : 0 < value (words 0) := by linarith only [hd, hDensity]
  have hNextMargin : guardMarginBudget (words 0) (words 1) (words 2) (words 3) <
      energyMargin (decodedState (words 0) (words 1) (words 2) (words 3)) := by
    rw [hState]
    linarith only [hm, hMargin]
  exact stateGuard_of_energyMargin (words 0) (words 1) (words 2) (words 3)
    (hFinite 0) (hFinite 1) (hFinite 2) (hFinite 3) hRho ht nr ne hNextMargin

#print axioms candidate_guard_sufficient
end Project.EulerRiemann.Numerics
