import Library.Numerics.Arithmetic.Fma.Program
import Verified.Reflect.Command

namespace Library.Numerics.Arithmetic.Fma.Fma

verified_compile compiled := [msb64, msb128, mul128, shl128, shr128, lowBits128, sticky128, bit128,
  lt128, add128, sub128, roundPack, fmaBits, fma]

end Library.Numerics.Arithmetic.Fma.Fma
