import Verified.Examples.FourierPositive

namespace Verified.Examples.FourierInverseBounds

open CodeLib.IEEE64 LeanExe.ProofKit F64Approx FourierSpec FourierLoop

set_option exponentiation.threshold 1200

theorem normalize_near (xs : Array Float) (h : Admissible xs) (hn : 0 < xs.size / 2)
    (y : Float) (R : ℝ) (hy : FApprox y R (errorBound xs))
    (hR : |R| ≤ inputNorm xs) :
    FApprox (y / (nWord xs).toFloat) (R / (xs.size / 2 : ℕ))
      ((errorBound xs + unitRoundoff64 * magnitudeBound xs) / (xs.size / 2 : ℕ) +
        multiplicationUnderflowEpsilon) := by
  have hn32 : nSamples xs ≤ 2 ^ 32 := h.1
  have hnreal : (0 : ℝ) < (xs.size / 2 : ℕ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (xs.size / 2 : ℕ) := by
    exact_mod_cast (show 1 ≤ xs.size / 2 from hn)
  have hden := FourierTwiddle.convert_near (nWord xs) ((nWord_le xs hn32).trans (by norm_num))
  rw [nWord_toNat xs hn32] at hden
  change FApprox (nWord xs).toFloat (xs.size / 2 : ℕ) 0 at hden
  have hM : 0 ≤ magnitudeBound xs := by
    rw [magnitudeBound_eq_inputNorm_add_errorBound]
    exact add_nonneg (inputNorm_nonneg xs) (errorBound_nonneg xs)
  have hcap : magnitudeBound xs / (xs.size / 2 : ℕ) < (2 : ℝ) ^ 1022 :=
    (div_le_self hM hn1).trans_lt h.2.2
  have hd := fapprox_div hy hden (inputNorm xs) (xs.size / 2 : ℕ) hR
    (by rw [abs_of_pos hnreal]) hnreal (magnitudeBound xs / (xs.size / 2 : ℕ))
    (by rw [sub_zero, ← magnitudeBound_eq_inputNorm_add_errorBound]) hcap
  simp only [mul_zero, zero_div, add_zero, sub_zero] at hd
  exact hd.mono (le_of_eq (by
    unfold unitRoundoff64 multiplicationUnderflowEpsilon
    ring))

#print axioms normalize_near

end Verified.Examples.FourierInverseBounds
