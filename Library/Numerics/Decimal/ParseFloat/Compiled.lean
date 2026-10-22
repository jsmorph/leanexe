import Library.Numerics.Decimal.ParseFloat.Program
import Verified.Reflect.Command

namespace Library.Numerics.Decimal.ParseFloat

open Library.Numerics.Arithmetic.Uscale

verified_compile compiled := [limb, mulSmall, shl, cmpStep, le, sub, wordBits, bitLen, divStep,
  divBits, scaledQuot, pow10Word, mulPow10, isDigitW, isHexW, hexValW, lowerW, span, matchLower,
  expDigits, expPart, digitPos, leadingZeros, anyNonzero, chunkVal, digitsVal, hexVal, roundUnits,
  decRound, decParse, hexParse, pow10Float, fastPath, parse64, parse32]

end Library.Numerics.Decimal.ParseFloat
