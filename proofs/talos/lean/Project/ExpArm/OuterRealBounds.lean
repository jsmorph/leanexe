import Project.ExpArm.IntegerSelection
import Project.ProofKit.F64Accuracy

namespace Project.ExpArm
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem real_exp_large (x : ℝ) (hx : 800 ≤ x) : (2 : ℝ)^1024 < Real.exp x := by
  have hl : Real.log 2 ≤ 7/10 := by linarith [log_quotient_bounds.2]
  have h := Real.exp_lt_exp.mpr (show (1024 : Nat)*Real.log 2 < x by push_cast; linarith)
  rwa [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h

theorem real_exp_small (x : ℝ) (hx : x ≤ -800) : Real.exp x < (2 : ℝ)^(-1074 : Int) := by
  have hl : Real.log 2 ≤ 7/10 := by linarith [log_quotient_bounds.2]
  have h := Real.exp_lt_exp.mpr (show x < -((1074 : Nat)*Real.log 2) by push_cast; linarith)
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  simpa using h

theorem zero_accuracy (x : ℝ) (hx : x ≤ -800) : Project.ProofKit.F64Accuracy.ErrorBelowOneUlp 0 (Real.exp x) := by
  apply Project.ProofKit.F64Accuracy.of_subnormal_error _ _ (by rfl) (Real.exp_pos _)
  have hz : value 0 = 0 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.sign,
      Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  rw [hz, zero_sub, abs_neg, abs_of_pos (Real.exp_pos _)]
  exact real_exp_small x hx

#print axioms real_exp_large
#print axioms zero_accuracy
end Project.ExpArm
