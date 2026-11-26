module

public import Library.Numerics.Decimal.PrintFloat.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Decimal.PrintFloat

open Library.Numerics.Arithmetic.Uscale

verified_compile compiled := [limb, mulSmall, shl, cmpStep, le, sub, wordBits, bitLen, divStep,
  divBits, scaledQuot, pow10Word, mulPow10, limbsOf, quotAt, range, found, nearest, clamp, startExp,
  shortest, numDigits, digitAt, digitsFrom, byte1, noBytes, zeros, sciLayoutW, ecmaLayoutW, fixed,
  special, print64With, print32With, print64, print64Ecma, print32, print32Ecma]

end Library.Numerics.Decimal.PrintFloat
