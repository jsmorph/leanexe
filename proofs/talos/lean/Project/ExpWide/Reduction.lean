import Project.ExpWide.Model
import Project.ExpSmall.Numerical
import Project.ProofKit.F64UnitInterval

namespace Project.ExpWide
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem eight_value : value 0x4020000000000000 = 8 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem reduction (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 8) :
    Finite (Wasm.IEEE64.div x 0x4020000000000000) ∧
    |value (Wasm.IEEE64.div x 0x4020000000000000)| ≤ 1 ∧
    |value (Wasm.IEEE64.div x 0x4020000000000000) - value x / 8| ≤ arithmeticEpsilon := by
  have hq : |value x / value 0x4020000000000000| ≤ 1 := by
    rw [eight_value, abs_div]
    norm_num
    linarith
  have hs := F64DivBounds.div_real_mixed x 0x4020000000000000 hf
    (by unfold CodeLib.IEEE64.Finite; decide)
    (by decide) (hq.trans_lt (by norm_num))
  have he : |value (Wasm.IEEE64.div x 0x4020000000000000) - value x / 8| ≤
      unitRoundoff64 + multiplicationUnderflowEpsilon := by
    rw [eight_value] at hs hq
    exact hs.2.trans (by nlinarith [show 0 ≤ unitRoundoff64 by norm_num [unitRoundoff64]])
  have hu : unitRoundoff64 + multiplicationUnderflowEpsilon < arithmeticEpsilon := by
    norm_num [unitRoundoff64, multiplicationUnderflowEpsilon, arithmeticEpsilon]
  refine ⟨hs.1, F64UnitInterval.abs_le_one_of_lt_successor _ ?_, he.trans hu.le⟩
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ 1 he (by simpa [eight_value] using hq)
  linarith

theorem perturbed_exp (x y error : ℝ) (hx : x ≤ 0)
    (he : |y-x| ≤ error) (hu : error ≤ 1) :
    |Real.exp y - Real.exp x| ≤ 2 * error := by
  have h := Real.abs_exp_sub_one_le (he.trans hu)
  have hp := (Real.exp_pos x).le
  have hx1 : Real.exp x ≤ 1 := by simpa using Real.exp_le_exp.mpr hx
  have hid : Real.exp y - Real.exp x = Real.exp x * (Real.exp (y-x)-1) := by
    rw [mul_sub, ← Real.exp_add]
    rw [show x + (y-x) = y by ring, mul_one]
  rw [hid, abs_mul, abs_of_nonneg hp]
  have herror : |Real.exp (y-x)-1| ≤ 2 * error := h.trans (by linarith)
  have hh := mul_le_mul_of_nonneg_left herror hp
  have hn : 0 ≤ error := (abs_nonneg _).trans he
  nlinarith

theorem reduced_polynomial (x : UInt64) (hf : Finite x)
    (hl : -8 ≤ value x) (hu : value x ≤ 0) :
    Finite (ExpSmall.polynomial (Wasm.IEEE64.div x 0x4020000000000000)) ∧
    |value (ExpSmall.polynomial (Wasm.IEEE64.div x 0x4020000000000000)) -
      Real.exp (value x / 8)| ≤ 1 / 3990 := by
  have hr := reduction x hf (abs_le.mpr ⟨hl, by linarith⟩)
  have hp := ExpSmall.polynomial_error _ hr.1 hr.2.1
  have he := perturbed_exp (value x/8) (value (Wasm.IEEE64.div x 0x4020000000000000))
    arithmeticEpsilon (by linarith) hr.2.2 (by norm_num [arithmeticEpsilon])
  refine ⟨hp.1, (abs_sub_le _ _ _).trans ((add_le_add hp.2 he).trans ?_)⟩
  norm_num [arithmeticEpsilon]

#print axioms reduction
#print axioms reduced_polynomial
end Project.ExpWide
