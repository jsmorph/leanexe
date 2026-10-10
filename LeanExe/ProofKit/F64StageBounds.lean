import LeanExe.ProofKit.F64ArithmeticBounds

/-!
One rounded product or sum in a chain of bounded operations: from bounds on the operands' values
and a cap `M` on the exact result, the rounded result is finite, its magnitude is bounded, and
its error is at most `arithmeticEpsilon * M`.
-/

namespace LeanExe.ProofKit.F64StageBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem mul_stage (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (A B M : ℝ) (hA : |value a| ≤ A) (hB : |value b| ≤ B)
    (hM : A * B ≤ M) (hmin : minNormal64 ≤ M) (hmax : M < (2 : ℝ) ^ 1022) :
    Finite (Wasm.IEEE64.mul a b) ∧
    |value (Wasm.IEEE64.mul a b)| ≤ A * B + arithmeticEpsilon * M ∧
    |value (Wasm.IEEE64.mul a b) - value a * value b| ≤ arithmeticEpsilon * M := by
  have hp : |value a * value b| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul hA hB (abs_nonneg _) ((abs_nonneg _).trans hA)
  have he := F64ArithmeticBounds.mul_error_scaled a b ha hb M hmin hmax (hp.trans hM)
  exact ⟨he.1, F64ArithmeticBounds.magnitude_of_error _ _ _ _ he.2 hp, he.2⟩

theorem add_stage (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (A B M : ℝ) (hA : |value a| ≤ A) (hB : |value b| ≤ B)
    (hM : A + B ≤ M) (hmax : M < (2 : ℝ) ^ 1023) :
    Finite (Wasm.IEEE64.add a b) ∧
    |value (Wasm.IEEE64.add a b)| ≤ A + B + arithmeticEpsilon * M ∧
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ arithmeticEpsilon * M := by
  have hp : |value a + value b| ≤ A + B :=
    (abs_add_le _ _).trans (add_le_add hA hB)
  have he := F64ArithmeticBounds.add_error_scaled a b ha hb M hmax (hp.trans hM)
  exact ⟨he.1, F64ArithmeticBounds.magnitude_of_error _ _ _ _ he.2 hp, he.2⟩

#print axioms mul_stage
#print axioms add_stage

end LeanExe.ProofKit.F64StageBounds
