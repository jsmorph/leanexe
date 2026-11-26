module

public import Library.Numerics.Float64.Tgamma.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Float64.Tgamma

set_option maxHeartbeats 1000000 in
verified_compile compiled := [Library.Numerics.Arithmetic.Fma.msb64, Library.Numerics.Arithmetic.Fma.msb128, Library.Numerics.Arithmetic.Fma.mul128, Library.Numerics.Arithmetic.Fma.shl128, Library.Numerics.Arithmetic.Fma.shr128,
 Library.Numerics.Arithmetic.Fma.lowBits128, Library.Numerics.Arithmetic.Fma.sticky128, Library.Numerics.Arithmetic.Fma.bit128, Library.Numerics.Arithmetic.Fma.lt128, Library.Numerics.Arithmetic.Fma.add128, Library.Numerics.Arithmetic.Fma.sub128, Library.Numerics.Arithmetic.Fma.roundPack,
 Library.Numerics.Arithmetic.Fma.fmaBits, Library.Numerics.Arithmetic.Fma.fma, entry, fastTwoSum, twoSum, fastSum, sumDD, mulDD, mulDD3, mulDDD, polyDDD,
 splt, sprod, poly3, roundEven, floorF, toWord, sar, nonPositive, asLogd, asSinpid, asExpd,
 asLgammaAsym, database, accurateRange, accurate, tgammaWith, tgamma]

end Library.Numerics.Float64.Tgamma
