import Project.EulerRiemann.ReconstructionResidual
import Project.ProofKit.F64Halving

namespace Project.EulerRiemann.Reconstruction
open CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (State)
open Project.ProofKit.F64Halving

theorem factorAfter_bounded (steps : Nat) (factor : UInt64) (h : Bounded factor) :
    Bounded (factorAfter steps factor) ∧
      Wasm.IEEE64.scaledMagnitude (factorAfter steps factor) ≤
        Wasm.IEEE64.scaledMagnitude factor := by
  induction steps generalizing factor with
  | zero => exact ⟨h, le_rfl⟩
  | succ steps ih =>
      have hh := half_preserves h
      have hi := ih _ hh.1
      exact ⟨hi.1, hi.2.trans hh.2⟩

theorem factorAfter_value (steps : Nat) :
    Finite (factorAfter steps 0x3FE0000000000000) ∧
      0 ≤ value (factorAfter steps 0x3FE0000000000000) ∧
      value (factorAfter steps 0x3FE0000000000000) ≤ 1/2 := by
  have h := (factorAfter_bounded steps _ half_bounded).1
  exact ⟨h.1, bounded_value h⟩

theorem factorAfter_nonincreasing (steps : Nat) (factor : UInt64) (h : Bounded factor) :
    value (factorAfter steps factor) ≤ value factor := by
  have hs := factorAfter_bounded steps factor h
  simp only [value, Wasm.IEEE64.scaledValue, hs.1.2.1, h.2.1,
    Bool.false_eq_true, ite_false, Int.cast_natCast]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hs.2) (by positivity)

theorem reconstruct_factor_bounded (fuel : Nat) (left center right : State) :
    Bounded (reconstruct fuel left center right).factor := by
  rcases reconstruct_behavior fuel left center right with hr | hs
  · rw [hr]
    exact zero_bounded
  · rcases reconstruct_certificate fuel left center right hs.1 with hc |
        ⟨steps, _, hfactor, _⟩
    · rw [hc]
      exact zero_bounded
    · rw [hfactor]
      exact (factorAfter_bounded steps _ half_bounded).1

theorem reconstruct_factor (fuel : Nat) (left center right : State) :
    Finite (reconstruct fuel left center right).factor ∧
      0 ≤ value (reconstruct fuel left center right).factor ∧
      value (reconstruct fuel left center right).factor ≤ 1/2 := by
  have h := reconstruct_factor_bounded fuel left center right
  exact ⟨h.1, bounded_value h⟩

#print axioms factorAfter_bounded
#print axioms factorAfter_value
#print axioms factorAfter_nonincreasing
#print axioms reconstruct_factor
end Project.EulerRiemann.Reconstruction
