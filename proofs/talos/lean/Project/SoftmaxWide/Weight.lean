import Project.SoftmaxWide.Model
import Project.ExpNeg.Numerical
import Project.ProofKit.RealExponential

namespace Project.SoftmaxWide
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem subtract_max (x m : UInt64) (hx : Finite x) (hm : Finite m)
    (hab : |value x-value m| < (2:ℝ)^1023) (ho : value x ≤ value m) :
    Finite (Wasm.IEEE64.sub x m) ∧ value (Wasm.IEEE64.sub x m) ≤ 0 ∧
    |value (Wasm.IEEE64.sub x m)-(value x-value m)| ≤ arithmeticEpsilon*|value x-value m| := by
  have hs := F64AddBounds.sub_real_relative x m hx hm hab
  have he := (abs_le.mp hs.2).2
  rw [abs_of_nonpos (sub_nonpos.mpr ho)] at he
  refine ⟨hs.1, ?_, hs.2.trans ?_⟩
  · norm_num [unitRoundoff64] at he
    linarith
  · exact mul_le_mul_of_nonneg_right (by norm_num [unitRoundoff64, arithmeticEpsilon]) (abs_nonneg _)

theorem shifted_weight (x m : UInt64) (hx : Finite x) (hm : Finite m)
    (hab : |value x-value m| < (2:ℝ)^1023) (ho : value x ≤ value m) :
    let w := ExpNeg.evaluate (Wasm.IEEE64.sub x m)
    Finite w ∧ 0 ≤ value w ∧ value w ≤ 2 ∧
    |value w-Real.exp (value x-value m)| ≤
      5000*arithmeticEpsilon*Real.exp (value x-value m)+1/10^27 := by
  let d := value x-value m
  let y := Wasm.IEEE64.sub x m
  have hd : d ≤ 0 := sub_nonpos.mpr ho
  have hs := subtract_max x m hx hm hab ho
  have he := ExpNeg.evaluate_error y hs.1 hs.2.1
  have hy1 : Real.exp (value y) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr hs.2.1
  have hsmall : value (ExpNeg.evaluate y) ≤ 2 := by
    have hh := (abs_le.mp he.2.2).2
    have hh2 := mul_le_mul_of_nonneg_left hy1
      (by norm_num [arithmeticEpsilon] : 0 ≤ 4029*arithmeticEpsilon)
    have ht := ExpNeg.tail_bound
    norm_num [arithmeticEpsilon] at hh hh2
    linarith
  refine ⟨he.1, he.2.1, hsmall, ?_⟩
  change |value (ExpNeg.evaluate y)-Real.exp d| ≤ 5000*arithmeticEpsilon*Real.exp d+1/10^27
  by_cases hl : -65 ≤ d
  · have hsabs : |value y-d| ≤ 65*arithmeticEpsilon := by
      have hh := hs.2.2
      change |value y-d| ≤ arithmeticEpsilon*|d| at hh
      rw [abs_of_nonpos hd] at hh
      have heps : 0 ≤ arithmeticEpsilon := by norm_num [arithmeticEpsilon]
      nlinarith
    have hp := RealExponential.relative_perturbation d (value y) (65*arithmeticEpsilon)
      hsabs (by norm_num [arithmeticEpsilon])
    have hupper := (abs_le.mp hp).2
    have herr := (abs_sub_le (value (ExpNeg.evaluate y)) (Real.exp (value y)) (Real.exp d)).trans
      (add_le_add he.2.2 hp)
    have ht := ExpNeg.tail_bound
    have hep := Real.exp_pos d
    norm_num [arithmeticEpsilon] at hupper herr ⊢
    linarith
  · have hy : value y < -64 := by
      have hh := (abs_le.mp hs.2.2).2
      change value y-d ≤ arithmeticEpsilon*|d| at hh
      rw [abs_of_nonpos hd] at hh
      norm_num [arithmeticEpsilon] at hh
      linarith
    rw [ExpNeg.evaluate_tail y hy, ExpSmall.zero_value, zero_sub,
      abs_neg, abs_of_pos (Real.exp_pos d)]
    have ht : Real.exp d ≤ 1/10^27 :=
      (Real.exp_le_exp.mpr (by linarith : d ≤ -64)).trans ExpNeg.tail_bound
    have hp : 0 ≤ 5000*arithmeticEpsilon*Real.exp d := by
      exact mul_nonneg (by norm_num [arithmeticEpsilon]) (Real.exp_pos d).le
    linarith

#print axioms shifted_weight
end Project.SoftmaxWide
