import Project.EulerRiemann.NumericsCellReference
import Project.EulerRiemann.NumericsReferenceBounds
import Project.EulerRiemann.NumericsRealStep
import Project.EulerRiemann.RealMarginBounds
import Project.EulerRiemann.RealPerturbation

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.Euler2DConservative.Guard (Vec4 decodedState)
open RealRusanov

def candidateWords (ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR : UInt64) : Fin 4 → UInt64 :=
  let left := fluxCheckedBits rhoL mxL myL energyL rho mx my energy
  let right := fluxCheckedBits rho mx my energy rhoR mxR myR energyR
  fun i => (Project.EulerCellStep.Model.updateCheckedBits ratio
    (stateWords rho mx my energy i) (fluxWords left i) (fluxWords right i)).value

theorem candidate_margin_bounds (ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (hr : positiveBits ratio = true) (br : value ratio ≤ 1)
    (hL : StateBounds M rhoL mxL myL energyL) (hC : StateBounds M rho mx my energy)
    (hR : StateBounds M rhoR mxR myR energyR) :
    let left := fluxCheckedBits rhoL mxL myL energyL rho mx my energy
    let right := fluxCheckedBits rho mx my energy rhoR mxR myR energyR
    let alpha := if left.alpha ≤ right.alpha then right.alpha else left.alpha
    let courant := Wasm.IEEE64.mul ratio alpha
    positiveBits courant = true → courant ≤ 0x3FE0000000000000 →
    let qC := decodedState rho mx my energy
    let reference := update (value ratio) (value left.alpha) (value right.alpha)
      (decodedState rhoL mxL myL energyL) qC (decodedState rhoR mxR myR energyR)
    let words := candidateWords ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR
    let next : Vec4 := fun i => value (words i)
    let weight := 1 - value ratio * (value left.alpha + value right.alpha) / 2
    let bound := M + 134 * value ratio * M^5
    let error := arithmeticEpsilon * M + 1004 * arithmeticEpsilon * value ratio * M^5 +
      2 * multiplicationUnderflowEpsilon
    (∀ i, Finite (words i)) ∧ (∀ i, |next i - reference i| ≤ error) ∧
      weight * value rho - error ≤ next 0 ∧
      weight^2 * energyMargin qC - (8 * bound * error + 4 * error^2) ≤ energyMargin next := by
  dsimp only
  intro hc hhalf
  let left := fluxCheckedBits rhoL mxL myL energyL rho mx my energy
  let right := fluxCheckedBits rho mx my energy rhoR mxR myR energyR
  let qC := decodedState rho mx my energy
  let reference := update (value ratio) (value left.alpha) (value right.alpha)
    (decodedState rhoL mxL myL energyL) qC (decodedState rhoR mxR myR energyR)
  let words := candidateWords ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR
  let next : Vec4 := fun i => value (words i)
  let weight := 1 - value ratio * (value left.alpha + value right.alpha) / 2
  let bound := M + 134 * value ratio * M^5
  let error := arithmeticEpsilon * M + 1004 * arithmeticEpsilon * value ratio * M^5 +
    2 * multiplicationUnderflowEpsilon
  have hFinite : ∀ i, Finite (words i) := fun i =>
    (cell_component_error ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR
      M hM hMmax hr br hL hC hR i).2.1
  have hError : ∀ i, |next i - reference i| ≤ error := fun i =>
    (cell_component_error ratio rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR
      M hM hMmax hr br hL hC hR i).2.2
  have hBound : ∀ i, |reference i| ≤ bound := reference_update_magnitude (value ratio)
    (positiveBits_spec ratio hr).2.le rhoL mxL myL energyL rho mx my energy rhoR mxR myR energyR
    M hM hMmax hL hC hR
  obtain ⟨hw, hd, hi, _⟩ := reference_step_weight ratio rhoL mxL myL energyL rho mx my energy
    rhoR mxR myR energyR M hM hMmax hr br hL hC hR hc hhalf
  change 49 / 100 ≤ weight at hw
  have hCenter := bounded_state_positive rho mx my energy M hM hC
  have hMargin := margin_weight_lower qC reference weight (by linarith only [hw])
    hCenter.1 hCenter.2.le hd hi
  have hPerturb := energyMargin_perturbation reference next bound error hBound hError
  refine ⟨hFinite, hError, ?_, ?_⟩
  · have he := (abs_le.mp (hError 0)).1
    change weight * value rho ≤ reference 0 at hd
    change weight * value rho - error ≤ next 0
    linarith only [he, hd]
  · have he := (abs_le.mp hPerturb).1
    change weight^2 * energyMargin qC - (8 * bound * error + 4 * error^2) ≤ energyMargin next
    linarith only [hMargin, he]

#print axioms candidate_margin_bounds
end Project.EulerRiemann.Numerics
