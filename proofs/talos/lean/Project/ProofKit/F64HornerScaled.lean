import Project.ProofKit.F64Horner

namespace Project.ProofKit.F64Horner
open CodeLib.IEEE64 F64ArithmeticBounds

set_option exponentiation.threshold 4096

theorem step_scaled {a x c : UInt64} {p q bound coefficientBound resultBound error coefficientError : ℝ}
    (ha : Approximation a p bound error)
    (hc : Approximation c q coefficientBound coefficientError)
    (hx : Finite x) (bx : |value x| ≤ 1)
    (hb : minNormal64 ≤ bound) (hu : bound ≤ 16) (hcmax : coefficientBound ≤ 16)
    (hout : bound + coefficientBound + (3*bound+coefficientBound)*arithmeticEpsilon ≤ resultBound) :
    Approximation (Wasm.IEEE64.add (Wasm.IEEE64.mul a x) c)
      (p*value x+q) resultBound
      (error+coefficientError+(3*bound+coefficientBound)*arithmeticEpsilon) := by
  have he0 : 0 ≤ arithmeticEpsilon := epsilon_pos.le
  have he1 : arithmeticEpsilon ≤ 1 := epsilon_small.le.trans (by norm_num)
  have hb0 : 0 ≤ bound := (abs_nonneg _).trans ha.magnitude
  have hp : |value a*value x| ≤ bound := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left bx (abs_nonneg _)).trans (by simpa using ha.magnitude)
  have hm := mul_error_scaled a x ha.finite hx bound hb (hu.trans_lt (by norm_num)) hp
  have bm : |value (Wasm.IEEE64.mul a x)| ≤ bound+arithmeticEpsilon*bound :=
    magnitude_of_error _ _ _ _ hm.2 hp
  have bs : |value (Wasm.IEEE64.mul a x)+value c| ≤ 2*bound+coefficientBound := by
    have ht := (abs_add_le _ _).trans (add_le_add bm hc.magnitude)
    nlinarith only [ht, mul_le_mul_of_nonneg_right he1 hb0]
  have hs := add_error_scaled _ c hm.1 hc.finite (2*bound+coefficientBound)
    (by
      calc
        _ ≤ 48 := by linarith
        _ < (2:ℝ)^1023 := by norm_num) bs
  have localError :
      |value (Wasm.IEEE64.add (Wasm.IEEE64.mul a x) c)-(value a*value x+value c)| ≤
        (3*bound+coefficientBound)*arithmeticEpsilon := by
    have ht := abs_add_le
      (value (Wasm.IEEE64.add (Wasm.IEEE64.mul a x) c)-(value (Wasm.IEEE64.mul a x)+value c))
      (value (Wasm.IEEE64.mul a x)-value a*value x)
    ring_nf at ht hm hs ⊢
    linarith only [ht, hm.2, hs.2]
  refine ⟨hs.1, ?_, ?_⟩
  · exact (magnitude_of_error _ _ _ _ localError
      ((abs_add_le _ _).trans (add_le_add hp hc.magnitude))).trans hout
  · have ep : |(value a-p)*value x| ≤ error := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left bx (abs_nonneg _)).trans (by simpa using ha.accuracy)
    have h₁ := abs_add_le ((value a-p)*value x) (value c-q)
    have h₂ := abs_add_le
      (value (Wasm.IEEE64.add (Wasm.IEEE64.mul a x) c)-(value a*value x+value c))
      ((value a-p)*value x+(value c-q))
    ring_nf at h₁ h₂ localError ep ⊢
    linarith only [h₁, h₂, localError, ep, hc.accuracy]

#print axioms step_scaled
end Project.ProofKit.F64Horner
