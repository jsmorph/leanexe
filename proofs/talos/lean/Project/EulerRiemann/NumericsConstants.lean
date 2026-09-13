import CodeLib.IEEE64.Roundoff

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem pressure_factor_finite : Finite 0x3FD999999999999A := by
  unfold CodeLib.IEEE64.Finite
  decide

theorem pressure_factor_value :
    value 0x3FD999999999999A = 2 / 5 + arithmeticEpsilon / 10 := by
  change ((7205759403792794 * 2^1020 : Nat) : ℝ) / (2 : ℝ)^1074 = _
  norm_num [arithmeticEpsilon]

theorem sound_factor_finite : Finite 0x3FF6666666666666 := by
  unfold CodeLib.IEEE64.Finite
  decide

theorem sound_factor_value :
    value 0x3FF6666666666666 = 7 / 5 - 2 * arithmeticEpsilon / 5 := by
  change ((6305039478318694 * 2^1022 : Nat) : ℝ) / (2 : ℝ)^1074 = _
  norm_num [arithmeticEpsilon]

#print axioms pressure_factor_value
#print axioms sound_factor_value
end Project.EulerRiemann.Numerics
