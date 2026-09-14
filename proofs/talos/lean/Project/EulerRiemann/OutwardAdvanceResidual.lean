import Project.EulerRiemann.OutwardAdvanceSpec
import Project.EulerRiemann.NumericsCellResidual

namespace Project.EulerRiemann.OutwardNumerics
open CodeLib.IEEE64
open Project.Euler2DDynamicFlux.Model (CheckedFlux)
open Project.Euler2DCellStep.Model (updateCheckedBits)
open Project.ProofKit.F64ConservativeUpdate
open Project.ProofKit.F64RoundingResidual (radius)
open Numerics (stateWords fluxWords cellWords)

theorem advance_update (ratio rho mx my energy : UInt64) (left right : CheckedFlux)
    (h : (advanceCheckedBits ratio rho mx my energy left right).status = 0) (i : Fin 4) :
    let state := stateWords rho mx my energy i
    let next := updateCheckedBits ratio state (fluxWords left i) (fluxWords right i)
    next.status = 0 ∧
      cellWords (advanceCheckedBits ratio rho mx my energy left right) i = next.value := by
  obtain ⟨_, _, _, _, _, _, hd, hm, ht, he, _⟩ :=
    advance_parts ratio rho mx my energy left right h
  dsimp only
  constructor
  · fin_cases i
    · exact hd
    · exact hm
    · exact ht
    · exact he
  · rw [advance_values ratio rho mx my energy left right h]
    fin_cases i <;> rfl

theorem advance_balance (ratio rho mx my energy : UInt64) (left right : CheckedFlux)
    (h : (advanceCheckedBits ratio rho mx my energy left right).status = 0) (i : Fin 4) :
    let state := stateWords rho mx my energy i
    let fluxL := fluxWords left i
    let fluxR := fluxWords right i
    let out := cellWords (advanceCheckedBits ratio rho mx my energy left right) i
    Certificate ratio state fluxL fluxR out ∧
      value out - value state =
        value ratio * (value fluxL - value fluxR) + residual ratio state fluxL fluxR out ∧
      |residual ratio state fluxL fluxR out| ≤
        |value ratio| * radius (Wasm.IEEE64.sub fluxR fluxL) +
        radius (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL)) + radius out := by
  obtain ⟨hs, hv⟩ := advance_update ratio rho mx my energy left right h i
  dsimp only
  refine ⟨?_, balance _ _ _ _ _, ?_⟩
  · rw [hv]
    exact Numerics.accepted_update_certificate _ _ _ _ hs
  · rw [hv]
    exact Numerics.accepted_update_residual_bound _ _ _ _ hs

#print axioms advance_update
#print axioms advance_balance
end Project.EulerRiemann.OutwardNumerics
