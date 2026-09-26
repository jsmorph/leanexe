import Project.EulerRiemann.FrozenNumericsConstants

namespace Project.EulerRiemann.Frozen.OutwardSpeed
open CodeLib.IEEE64
set_option exponentiation.threshold 4096

theorem half_value : value 0x3FE0000000000000 = (1:ℝ)/2 := by
  change ((2^1073:Nat):ℝ)/(2:ℝ)^1074 = 1/2
  norm_num

theorem pressure_factor_upper : (2:ℝ)/5 ≤ value 0x3FD999999999999A := by
  rw [Numerics.pressure_factor_value]
  have he : 0 ≤ arithmeticEpsilon := by norm_num [arithmeticEpsilon]
  linarith

theorem sound_factor_upper : (7:ℝ)/5 ≤ value 0x3FF6666666666667 := by
  change (7:ℝ)/5 ≤ ((6305039478318695*2^1022:Nat):ℝ)/(2:ℝ)^1074
  norm_num

#print axioms half_value
#print axioms pressure_factor_upper
#print axioms sound_factor_upper
end Project.EulerRiemann.Frozen.OutwardSpeed
