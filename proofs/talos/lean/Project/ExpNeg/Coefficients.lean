import Project.ProofKit.F64HornerScaled

namespace Project.ExpNeg
open CodeLib.IEEE64 Project.ProofKit.F64Horner

set_option exponentiation.threshold 4096

local macro "check_coefficient" : tactic =>
  `(tactic| {
    constructor
    · unfold CodeLib.IEEE64.Finite; decide
    all_goals norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]
  })

theorem coefficient18 : Approximation 0x3CA6827863B97D97 (1 / 6402373705728000)
    (1001 / (1000*6402373705728000)) ((1 / 6402373705728000)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient17 : Approximation 0x3CE952C77030AD4A (1 / 355687428096000)
    (1001 / (1000*355687428096000)) ((1 / 355687428096000)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient16 : Approximation 0x3D2AE7F3E733B81F (1 / 20922789888000)
    (1001 / (1000*20922789888000)) ((1 / 20922789888000)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient15 : Approximation 0x3D6AE7F3E733B81F (1 / 1307674368000)
    (1001 / (1000*1307674368000)) ((1 / 1307674368000)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient14 : Approximation 0x3DA93974A8C07C9D (1 / 87178291200)
    (1001 / (1000*87178291200)) ((1 / 87178291200)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient13 : Approximation 0x3DE6124613A86D09 (1 / 6227020800)
    (1001 / (1000*6227020800)) ((1 / 6227020800)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient12 : Approximation 0x3E21EED8EFF8D898 (1 / 479001600)
    (1001 / (1000*479001600)) ((1 / 479001600)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient11 : Approximation 0x3E5AE64567F544E4 (1 / 39916800)
    (1001 / (1000*39916800)) ((1 / 39916800)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient10 : Approximation 0x3E927E4FB7789F5C (1 / 3628800)
    (1001 / (1000*3628800)) ((1 / 3628800)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient9 : Approximation 0x3EC71DE3A556C734 (1 / 362880)
    (1001 / (1000*362880)) ((1 / 362880)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient8 : Approximation 0x3EFA01A01A01A01A (1 / 40320)
    (1001 / (1000*40320)) ((1 / 40320)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient7 : Approximation 0x3F2A01A01A01A01A (1 / 5040)
    (1001 / (1000*5040)) ((1 / 5040)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient6 : Approximation 0x3F56C16C16C16C17 (1 / 720)
    (1001 / (1000*720)) ((1 / 720)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient5 : Approximation 0x3F81111111111111 (1 / 120)
    (1001 / (1000*120)) ((1 / 120)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient4 : Approximation 0x3FA5555555555555 (1 / 24)
    (1001 / (1000*24)) ((1 / 24)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient3 : Approximation 0x3FC5555555555555 (1 / 6)
    (1001 / (1000*6)) ((1 / 6)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient2 : Approximation 0x3FE0000000000000 (1 / 2)
    (1001 / (1000*2)) ((1 / 2)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient1 : Approximation 0x3FF0000000000000 (1 / 1)
    (1001 / (1000*1)) ((1 / 1)*arithmeticEpsilon) := by
  check_coefficient

theorem coefficient0 : Approximation 0x3FF0000000000000 (1 / 1)
    (1001 / (1000*1)) ((1 / 1)*arithmeticEpsilon) := by
  check_coefficient

end Project.ExpNeg
