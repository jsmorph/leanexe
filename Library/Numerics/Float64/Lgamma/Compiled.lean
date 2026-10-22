import Library.Numerics.Float64.Lgamma.Program
import Verified.Reflect.Command

namespace Library.Numerics.Float64.Lgamma

open Tgamma (entry fastTwoSum twoSum fastSum sumDD mulDD mulDDD roundEven floorF)

set_option maxHeartbeats 1000000 in
verified_compile compiled := [Library.Numerics.Arithmetic.Fma.Fma.msb64, Library.Numerics.Arithmetic.Fma.Fma.msb128, Library.Numerics.Arithmetic.Fma.Fma.mul128, Library.Numerics.Arithmetic.Fma.Fma.shl128, Library.Numerics.Arithmetic.Fma.Fma.shr128,
  Library.Numerics.Arithmetic.Fma.Fma.lowBits128, Library.Numerics.Arithmetic.Fma.Fma.sticky128, Library.Numerics.Arithmetic.Fma.Fma.bit128, Library.Numerics.Arithmetic.Fma.Fma.lt128, Library.Numerics.Arithmetic.Fma.Fma.add128, Library.Numerics.Arithmetic.Fma.Fma.sub128, Library.Numerics.Arithmetic.Fma.Fma.roundPack,
  Library.Numerics.Arithmetic.Fma.Fma.fmaBits, Library.Numerics.Arithmetic.Fma.Fma.fma, Tgamma.entry, Tgamma.fastTwoSum, Tgamma.twoSum, Tgamma.fastSum,
  Tgamma.sumDD, Tgamma.mulDD, Tgamma.mulDDD, Tgamma.roundEven, Tgamma.floorF, Tgamma.asSinpid,
  copySign, polyDD, polyDDDFst, polyD, logReduce, asLogd, asLogdAccurate, asSinpipid,
  asSinpipidAccurate, asLgammaAsymAccurate, database, rootRange, accurate, piece, piecePoly,
  lgammaWith, lgammaFirstWith, lgammaR, lgamma]

end Library.Numerics.Float64.Lgamma
