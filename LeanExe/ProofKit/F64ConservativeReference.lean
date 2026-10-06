import LeanExe.ProofKit.F64ConservativeUpdate

/-! The error of a rounded conservative update against the exact update with exact fluxes. -/

namespace LeanExe.ProofKit.F64ConservativeUpdate
open CodeLib.IEEE64
open LeanExe.ProofKit.F64RoundingResidual (radius)

theorem reference_bound {ratio state fluxL fluxR output : UInt64}
    (h : Certificate ratio state fluxL fluxR output)
    (referenceL referenceR boundL boundR : ℝ)
    (hl : |value fluxL - referenceL| ≤ boundL)
    (hr : |value fluxR - referenceR| ≤ boundR) :
    |value output - (value state - value ratio * (referenceR - referenceL))| ≤
      |value ratio| * radius (Wasm.IEEE64.sub fluxR fluxL) +
      radius (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL)) + radius output +
      |value ratio| * (boundL + boundR) := by
  have heq : value output - (value state - value ratio * (referenceR - referenceL)) =
      residual ratio state fluxL fluxR output +
        value ratio * ((value fluxL - referenceL) - (value fluxR - referenceR)) := by
    unfold residual
    ring
  rw [heq]
  calc
    _ ≤ |residual ratio state fluxL fluxR output| +
        |value ratio * ((value fluxL - referenceL) - (value fluxR - referenceR))| :=
      abs_add_le _ _
    _ = |residual ratio state fluxL fluxR output| +
        |value ratio| * |(value fluxL - referenceL) - (value fluxR - referenceR)| := by
      rw [abs_mul]
    _ ≤ _ := by
      apply add_le_add (residual_bound h)
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (abs_sub _ _).trans (add_le_add hl hr)

end LeanExe.ProofKit.F64ConservativeUpdate
