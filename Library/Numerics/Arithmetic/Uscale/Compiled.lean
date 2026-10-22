import Library.Numerics.Arithmetic.Uscale.Program
import Verified.Reflect.Command

namespace Library.Numerics.Arithmetic.Uscale

verified_compile compiled := [mulSmall, shl, limb, cmpStep, le, sub, wordBits, bitLen,
  divStep, divBits, scaledQuot, pow10Word, mulPow10, pow10]

end Library.Numerics.Arithmetic.Uscale
