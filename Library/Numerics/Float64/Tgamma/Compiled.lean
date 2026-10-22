import Library.Numerics.Float64.Tgamma.Program
import Verified.Reflect.Command

namespace Library.Numerics.Float64.Tgamma

set_option maxHeartbeats 1000000 in
verified_compile compiled := [Library.Numerics.Arithmetic.Fma.Fma.msb64, Library.Numerics.Arithmetic.Fma.Fma.msb128, Library.Numerics.Arithmetic.Fma.Fma.mul128, Library.Numerics.Arithmetic.Fma.Fma.shl128, Library.Numerics.Arithmetic.Fma.Fma.shr128,
 Library.Numerics.Arithmetic.Fma.Fma.lowBits128, Library.Numerics.Arithmetic.Fma.Fma.sticky128, Library.Numerics.Arithmetic.Fma.Fma.bit128, Library.Numerics.Arithmetic.Fma.Fma.lt128, Library.Numerics.Arithmetic.Fma.Fma.add128, Library.Numerics.Arithmetic.Fma.Fma.sub128, Library.Numerics.Arithmetic.Fma.Fma.roundPack,
 Library.Numerics.Arithmetic.Fma.Fma.fmaBits, Library.Numerics.Arithmetic.Fma.Fma.fma, entry, fastTwoSum, twoSum, fastSum, sumDD, mulDD, mulDD3, mulDDD, polyDDD,
 splt, sprod, poly3, roundEven, floorF, toWord, sar, nonPositive, asLogd, asSinpid, asExpd,
 asLgammaAsym, database, accurateRange, accurate, tgammaWith, tgamma]

end Library.Numerics.Float64.Tgamma
