import Project.Gpt2CachedStep.LayerNorm.ForwardError

namespace Project.Gpt2CachedStep.LayerNorm.LowerBounds
open CodeLib.IEEE32

set_option exponentiation.threshold 512

theorem reference_root (X : Nat → ℝ) :
    1 / 1000 ≤ Project.Gpt2RowInvStd.DenominatorError.referenceRoot (ForwardError.referenceSquares X) := by
  apply Real.le_sqrt_of_sq_le
  have hn : 0 ≤ ForwardError.referenceSquares X := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (1 / 1000 : ℝ) ^ 2 ≤ CodeLib.IEEE32.value 0x3727C5AC := by
    norm_num [CodeLib.IEEE32.value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
      Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]
  exact he.trans (le_add_of_nonneg_left (div_nonneg hn (by norm_num)))

theorem root_sum (input : ByteArray) (X : Nat → ℝ) :
    1 / 1000 ≤ Real.sqrt (CodeLib.IEEE32.value (Project.Gpt2RowInvStd.DenominatorError.shifted
      (Project.Gpt2RowInvStd.variancePrefix input 0 (LeanExe.Models.Gpt2.rowMean input 0) 768))) +
        Project.Gpt2RowInvStd.DenominatorError.referenceRoot (ForwardError.referenceSquares X) :=
  (reference_root X).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))

theorem reference_inverse (X : Nat → ℝ) :
    0 ≤ ForwardError.referenceInverse X ∧ ForwardError.referenceInverse X ≤ 1000 := by
  have hr := reference_root X
  have hp : 0 < Project.Gpt2RowInvStd.DenominatorError.referenceRoot (ForwardError.referenceSquares X) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 1000) hr
  refine ⟨(one_div_pos.mpr hp).le, ?_⟩
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 1000) hr
  norm_num only [one_div_div, div_one] at hi
  exact hi

#print axioms reference_root
#print axioms root_sum
#print axioms reference_inverse
end Project.Gpt2CachedStep.LayerNorm.LowerBounds
