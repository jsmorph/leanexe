import Project.EulerRiemann.ReconstructionResidual
import Project.ProofKit.RealMinmodBounds

namespace Project.EulerRiemann.Reconstruction
open Project.Euler2DCellStep.Sweep (State)
open Project.ProofKit.F64RoundingResidual (radius)
open Project.ProofKit.F64SymmetricFaces (Certificate)
open CodeLib.IEEE64
noncomputable section

def decoded (state : State) : Fin 4 → ℝ := fun i => value (words state i)

def exactSlope (left center right : State) : Fin 4 → ℝ :=
  Project.ProofKit.RealMinmod.slope (decoded left) (decoded center) (decoded right)

def slopeRadius (left center right : State) (i : Fin 4) : ℝ :=
  max (radius (words (difference center left) i)) (radius (words (difference right center) i))

theorem slope_error (left center right : State) (hl : finiteState left = true)
    (hc : finiteState center = true) (hr : finiteState right = true)
    (hs : (slope left center right).status = 0) (i : Fin 4) :
    |value (words (slope left center right).state i) - exactSlope left center right i| ≤
      slopeRadius left center right i := by
  have hd := slope_accepted left center right hs
  have hb := (finiteState_iff _).mp hd.2.1 i
  have hf := (finiteState_iff _).mp hd.2.2 i
  rw [words_difference] at hb hf
  have heLeft := Project.ProofKit.F64RoundingResidual.sub_error (words center i) (words left i)
    ((finiteState_iff _).mp hc i) ((finiteState_iff _).mp hl i) hb
  have heRight := Project.ProofKit.F64RoundingResidual.sub_error (words right i) (words center i)
    ((finiteState_iff _).mp hr i) ((finiteState_iff _).mp hc i) hf
  rw [slope_value left center right hs i]
  unfold exactSlope Project.ProofKit.RealMinmod.slope decoded slopeRadius
  rw [words_difference, words_difference]
  exact (Project.ProofKit.RealMinmod.minmod_error _ _ _ _).trans
    (max_le_max heLeft heRight)

theorem face_errors_of_slope {factor center delta left right : UInt64}
    (h : Certificate factor center delta left right) (reference error : ℝ)
    (hd : |value delta - reference| ≤ error) :
    |value left - (value center - value factor * reference)| ≤
      radius (Wasm.IEEE64.mul factor delta) + radius left + |value factor| * error ∧
    |value right - (value center + value factor * reference)| ≤
      radius (Wasm.IEEE64.mul factor delta) + radius right + |value factor| * error := by
  have hf := Project.ProofKit.F64SymmetricFaces.face_errors h
  have hp : |value factor * value delta - value factor * reference| ≤ |value factor| * error := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hd (abs_nonneg _)
  have hll := (abs_le.mp hf.1).1
  have hlu := (abs_le.mp hf.1).2
  have hrl := (abs_le.mp hf.2).1
  have hru := (abs_le.mp hf.2).2
  have hpl := (abs_le.mp hp).1
  have hpu := (abs_le.mp hp).2
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem reconstruct_accuracy (fuel : Nat) (left center right : State)
    (h : (reconstruct fuel left center right).status = 0) :
    reconstruct fuel left center right = constantFaces center ∨
      ∃ steps < fuel,
        (reconstruct fuel left center right).factor = factorAfter steps 0x3FE0000000000000 ∧
        ∀ i : Fin 4,
          let out := reconstruct fuel left center right
          let delta := words (slope left center right).state i
          let offsetRadius := radius (Wasm.IEEE64.mul out.factor delta)
          (|decoded out.left i - (decoded center i - value out.factor * exactSlope left center right i)| ≤
            offsetRadius + radius (words out.left i) + |value out.factor| * slopeRadius left center right i ∧
          |decoded out.right i - (decoded center i + value out.factor * exactSlope left center right i)| ≤
            offsetRadius + radius (words out.right i) + |value out.factor| * slopeRadius left center right i) ∧
          |(decoded out.left i + decoded out.right i)/2 - decoded center i| ≤
            (radius (words out.left i) + radius (words out.right i))/2 := by
  rcases reconstruct_certificate fuel left center right h with hz | ⟨steps, hs, hf, hcert⟩
  · exact Or.inl hz
  · have hi := reconstruct_inputs fuel left center right h
    refine Or.inr ⟨steps, hs, hf, ?_⟩
    intro i
    have he := slope_error left center right
      (safe_finite _ (admissibleState_safe _ hi.1))
      (safe_finite _ (admissibleState_safe _ hi.2.1))
      (safe_finite _ (admissibleState_safe _ hi.2.2.1)) hi.2.2.2.1 i
    exact ⟨face_errors_of_slope (hcert i) _ _ he,
      Project.ProofKit.F64SymmetricFaces.average_error (hcert i)⟩

#print axioms slope_error
#print axioms face_errors_of_slope
#print axioms reconstruct_accuracy

end
end Project.EulerRiemann.Reconstruction
