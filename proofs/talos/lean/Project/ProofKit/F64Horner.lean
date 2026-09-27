import Project.ProofKit.F64ArithmeticBounds

namespace Project.ProofKit.F64Horner
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

structure Approximation (word : UInt64) (exactValue bound error : ℝ) : Prop where
  finite : Finite word
  magnitude : |value word| ≤ bound
  accuracy : |value word - exactValue| ≤ error

theorem step {a x c : UInt64} {p q bound error coefficientError : ℝ}
    (ha : Approximation a p bound error) (hc : Approximation c q 1 coefficientError)
    (hx : Finite x) (bx : |value x| ≤ 1) (hb : bound ≤ 16) :
    Approximation (Wasm.IEEE64.add (Wasm.IEEE64.mul a x) c)
      (p * value x + q) (bound + 2) (error + coefficientError + 34 * arithmeticEpsilon) := by
  have heps : 0 ≤ arithmeticEpsilon ∧ 34 * arithmeticEpsilon ≤ 1 := by
    norm_num [arithmeticEpsilon]
  have ba : |value a| ≤ 16 := ha.magnitude.trans hb
  have bprod : |value a * value x| ≤ bound := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left bx (abs_nonneg _)).trans (by simpa using ha.magnitude)
  obtain ⟨hf, he⟩ := F64ArithmeticBounds.mul_error a x ha.finite hx 16
    (by norm_num) (by norm_num) (bprod.trans hb)
  have bp : |value (Wasm.IEEE64.mul a x)| ≤ bound + 16 * arithmeticEpsilon :=
    F64ArithmeticBounds.magnitude_of_error _ _ _ _ (by simpa [mul_comm] using he) bprod
  have bsum : |value (Wasm.IEEE64.mul a x) + value c| ≤ 18 := by
    have h := abs_add_le (value (Wasm.IEEE64.mul a x)) (value c)
    linarith [hc.magnitude]
  obtain ⟨hs, es⟩ := F64ArithmeticBounds.add_error _ c hf hc.finite 18
    (by norm_num) (by norm_num) bsum
  have localError :
      |value (Wasm.IEEE64.add (Wasm.IEEE64.mul a x) c) - (value a * value x + value c)| ≤
        34 * arithmeticEpsilon := by
    have h := abs_add_le
      (value (Wasm.IEEE64.add (Wasm.IEEE64.mul a x) c) -
        (value (Wasm.IEEE64.mul a x) + value c))
      (value (Wasm.IEEE64.mul a x) - value a * value x)
    ring_nf at h he es ⊢
    linarith
  refine ⟨hs, ?_, ?_⟩
  · have b := abs_add_le (value a * value x) (value c)
    have h := F64ArithmeticBounds.magnitude_of_error _ _ _ _ localError
      (b.trans (add_le_add bprod hc.magnitude))
    linarith
  · have ep : |(value a - p) * value x| ≤ error := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left bx (abs_nonneg _)).trans
        (by simpa using ha.accuracy)
    have h₁ := abs_add_le ((value a - p) * value x) (value c - q)
    have h₂ := abs_add_le
      (value (Wasm.IEEE64.add (Wasm.IEEE64.mul a x) c) -
        (value a * value x + value c))
      ((value a - p) * value x + (value c - q))
    ring_nf at h₁ h₂ localError ep ⊢
    linarith [hc.accuracy]

#print axioms step
end Project.ProofKit.F64Horner
