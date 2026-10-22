import Library.Numerics.Float64.Erfc.Program
import Verified.Reflect.Command

namespace Library.Numerics.Float64.Erfc

verified_compile compiled := [Library.Numerics.Arithmetic.Fma.Fma.msb64, Library.Numerics.Arithmetic.Fma.Fma.msb128, Library.Numerics.Arithmetic.Fma.Fma.mul128, Library.Numerics.Arithmetic.Fma.Fma.shl128, Library.Numerics.Arithmetic.Fma.Fma.shr128,
 Library.Numerics.Arithmetic.Fma.Fma.lowBits128, Library.Numerics.Arithmetic.Fma.Fma.sticky128, Library.Numerics.Arithmetic.Fma.Fma.bit128, Library.Numerics.Arithmetic.Fma.Fma.lt128, Library.Numerics.Arithmetic.Fma.Fma.add128, Library.Numerics.Arithmetic.Fma.Fma.sub128, Library.Numerics.Arithmetic.Fma.Fma.roundPack,
 Library.Numerics.Arithmetic.Fma.Fma.fmaBits, Library.Numerics.Arithmetic.Fma.Fma.fma, entry, roundEven, floorF, toWord, sar, pow2, ldexp, fastTwoSum, twoSum,
 aMul, sMul, dMul, fastSum, erfFastTiny, erfFastMain, erfFast, mulZ2, tinyCoeff,
 erfAccurateTiny, erfAccurate, q1, exp1, expAccurate, asymptIndex, erfcAsymptFast, erfcFast,
 hardCase, asymptAccIndex, asymptAccurate, erfcAsymptAccurate, erfcAccurate, erfcMain, erfcWith,
 erfc]

end Library.Numerics.Float64.Erfc
