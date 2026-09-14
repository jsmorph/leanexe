import Project.EulerRiemann.ReconstructionSlope
import Project.ProofKit.F64SymmetricFaces

namespace Project.EulerRiemann.Reconstruction
open Project.Euler2DCellStep.Sweep (State)
open Project.ProofKit.F64Order (finiteBits_iff)
open Project.ProofKit.F64SymmetricFaces (Certificate)
open CodeLib.IEEE64

def factorAfter : Nat → UInt64 → UInt64
  | 0, factor => factor
  | steps+1, factor => factorAfter steps (Wasm.IEEE64.mul 0x3FE0000000000000 factor)

theorem limit_selected (fuel : Nat) (center delta : State) (factor : UInt64) :
    limit fuel center delta factor = constantFaces center ∨
      ∃ steps < fuel,
        limit fuel center delta factor = candidate center delta (factorAfter steps factor) ∧
        (candidate center delta (factorAfter steps factor)).status = 0 := by
  induction fuel generalizing factor with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
      simp only [limit, beq_iff_eq]
      split_ifs with h
      · exact Or.inr ⟨0, Nat.zero_lt_succ fuel, rfl, h⟩
      · rcases ih (Wasm.IEEE64.mul 0x3FE0000000000000 factor) with hc | ⟨steps, hs, heq, ha⟩
        · exact Or.inl hc
        · exact Or.inr ⟨steps+1, Nat.succ_lt_succ hs, heq, ha⟩

theorem candidate_certificate (center delta : State) (factor : UInt64)
    (hc : finiteState center = true) (hd : finiteState delta = true)
    (h : (candidate center delta factor).status = 0) (i : Fin 4) :
    Certificate factor (words center i) (words delta i)
      (words (candidate center delta factor).left i)
      (words (candidate center delta factor).right i) := by
  have hg := candidate_accepted center delta factor h
  have hf := (finiteBits_iff factor).mp hg.2.1
  have ho := (finiteState_iff _).mp hg.2.2.1 i
  have hl := (finiteState_iff _).mp (safe_finite _ (admissibleState_safe _ hg.2.2.2.1)) i
  have hr := (finiteState_iff _).mp (safe_finite _ (admissibleState_safe _ hg.2.2.2.2)) i
  rw [words_scale] at ho
  rw [words_difference, words_scale] at hl
  rw [words_sum, words_scale] at hr
  rw [hg.1]
  simp only [words_difference, words_sum, words_scale]
  exact Project.ProofKit.F64SymmetricFaces.rounded_faces factor (words center i) (words delta i)
    hf ((finiteState_iff center).mp hc i) ((finiteState_iff delta).mp hd i) ho hl hr

theorem reconstruct_certificate (fuel : Nat) (left center right : State)
    (h : (reconstruct fuel left center right).status = 0) :
    reconstruct fuel left center right = constantFaces center ∨
      ∃ steps < fuel,
        (reconstruct fuel left center right).factor = factorAfter steps 0x3FE0000000000000 ∧
        ∀ i : Fin 4, Certificate (reconstruct fuel left center right).factor
          (words center i) (words (slope left center right).state i)
          (words (reconstruct fuel left center right).left i)
          (words (reconstruct fuel left center right).right i) := by
  have hi := reconstruct_inputs fuel left center right h
  rw [hi.2.2.2.2]
  rcases limit_selected fuel center (slope left center right).state 0x3FE0000000000000 with
    hz | ⟨steps, hs, heq, ha⟩
  · exact Or.inl hz
  · rw [heq]
    have hc := candidate_accepted center (slope left center right).state
      (factorAfter steps 0x3FE0000000000000) ha
    have hfactor : (candidate center (slope left center right).state
        (factorAfter steps 0x3FE0000000000000)).factor = factorAfter steps 0x3FE0000000000000 := by
      rw [hc.1]
    refine Or.inr ⟨steps, hs, hfactor, ?_⟩
    intro i
    rw [hfactor]
    exact candidate_certificate center (slope left center right).state _
      (safe_finite _ (admissibleState_safe center hi.2.1))
      (slope_finite left center right hi.2.2.2.1) ha i

#print axioms limit_selected
#print axioms candidate_certificate
#print axioms reconstruct_certificate

end Project.EulerRiemann.Reconstruction
