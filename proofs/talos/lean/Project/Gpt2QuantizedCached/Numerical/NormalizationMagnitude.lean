import Project.Gpt2QuantizedCached.Numerical.NormalizationPairUpper
import Project.ProofKit.F32Absolute

namespace Project.Gpt2QuantizedCached.Numerical.NormalizationUpper
open Project.ProofKit Gpt2CachedStep.LayerNorm

theorem raw_magnitude (a : UInt32) (m : Nat) (h : Wasm.IEEE32.scaledMagnitude a ≤ m) :
    |CodeLib.IEEE32.value a| ≤ DyadicUpper.value (DyadicUpper.fp32Magnitude m) := by
  rw [F32Order.abs_value_scaledMagnitude, DyadicUpper.fp32Magnitude_value]
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

theorem real_center (X : Nat → ℝ) (M : Nat) (h : ∀ i < 768, |X i| ≤ DyadicUpper.value M) (i : Nat) (hi : i < 768) :
    |X i - ForwardError.referenceMean X| ≤ DyadicUpper.value (2 * M) := by
  have hs : |∑ j ∈ Finset.range 768, X j| ≤ 768 * DyadicUpper.value M := by
    calc
      _ ≤ ∑ j ∈ Finset.range 768, |X j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range 768, DyadicUpper.value M := Finset.sum_le_sum fun j hj => h j (Finset.mem_range.mp hj)
      _ = _ := by simp
  have hm : |ForwardError.referenceMean X| ≤ DyadicUpper.value M := by
    unfold ForwardError.referenceMean
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 768)]
    linarith
  have hd := (abs_sub_le (X i) 0 (ForwardError.referenceMean X))
  simp only [sub_zero, zero_sub, abs_neg] at hd
  rw [DyadicUpper.timesNat_value]
  norm_num only [Nat.cast_ofNat]
  linarith [h i hi]

#print axioms raw_magnitude
#print axioms real_center
end Project.Gpt2QuantizedCached.Numerical.NormalizationUpper
