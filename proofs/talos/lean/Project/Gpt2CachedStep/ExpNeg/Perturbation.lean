import Project.Gpt2CachedStep.ExpNeg.ForwardError
import Project.ProofKit.RealExpPerturbation

namespace Project.Gpt2CachedStep.ExpNeg.Perturbation
open Project.ProofKit CodeLib.IEEE32 LeanExe.Models.Gpt2

theorem exp_error (input : UInt32) (reference inputError : ℝ)
    (mulBounds addBounds squareBounds : Nat → Nat)
    (hCutoff : input > 0xC2800000 → value input ≤ -64)
    (hRanges : input ≤ 0xC2800000 → ForwardError.Ranges input mulBounds addBounds squareBounds)
    (hNonpositive : value input ≤ 0) (hReference : reference ≤ 0)
    (hInputError : |value input - reference| ≤ inputError) :
    CodeLib.IEEE32.Finite (expNeg input) ∧
      |value (expNeg input) - Real.exp reference| ≤
        ForwardError.error input mulBounds addBounds squareBounds + inputError := by
  have h := ForwardError.exp_error input mulBounds addBounds squareBounds hCutoff hRanges
  have hPerturbation := (RealExpPerturbation.nonpositive (value input) reference hNonpositive hReference).trans hInputError
  exact ⟨h.1, (abs_sub_le _ _ _).trans (add_le_add h.2 hPerturbation)⟩

#print axioms exp_error
end Project.Gpt2CachedStep.ExpNeg.Perturbation
