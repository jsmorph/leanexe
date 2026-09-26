import Project.ProofKit.F32PairError

namespace Project.ProofKit.F32SqrtError
open CodeLib.IEEE32

theorem error (a : UInt32) (reference inputError lower : ℝ) (bound : Nat)
    (ha : CodeLib.IEEE32.Finite a) (hSign : Wasm.IEEE32.sign a = false)
    (hLower : 24 ≤ bound) (hUpper : bound ≤ 274)
    (hRange : Wasm.IEEE32.scaledMagnitude a * 2 ^ 149 ≤ 2 ^ (2 * bound))
    (hReference : 0 ≤ reference) (hl : 0 < lower)
    (hDen : lower ≤ Real.sqrt (value a) + Real.sqrt reference)
    (hError : |value a - reference| ≤ inputError) :
    CodeLib.IEEE32.Finite (LeanExe.Float32.sqrtBits a) ∧
      |value (LeanExe.Float32.sqrtBits a) - Real.sqrt reference| ≤
        F32SqrtBounds.epsilon bound + inputError / lower := by
  have hRound := F32SqrtBounds.sqrt_real_error a bound hLower hUpper ha hSign hRange
  have hNonneg : 0 ≤ value a := by
    simp only [value, Wasm.IEEE32.scaledValue, hSign, Bool.false_eq_true, ite_false]
    positivity
  have hPerturbation := F32PairError.sqrt_perturbation (value a) reference inputError lower
    hNonneg hReference hl hDen hError
  exact ⟨hRound.1, (abs_sub_le _ _ _).trans (add_le_add hRound.2 hPerturbation)⟩

#print axioms error
end Project.ProofKit.F32SqrtError
