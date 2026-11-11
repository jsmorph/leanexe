import Demos.Sgp4.Omm
import Verified.Reflect.Command
import Library.Numerics.Interval.Encoding

namespace Demos.Sgp4.Omm

open Library.Numerics.Decimal.ParseFloat Library.Numerics.Arithmetic.Uscale in
verified_compile compiled := [limb, mulSmall, shl, cmpStep, le, sub, wordBits, bitLen, divStep,
  divBits, scaledQuot, pow10Word, mulPow10, isDigitW, isHexW, hexValW, lowerW, span, matchLower,
  expDigits, expPart, digitPos, leadingZeros, anyNonzero, chunkVal, digitsVal, hexVal, roundUnits,
  decRound, decParse, hexParse, pow10Float, fastPath, parse64, Library.Numerics.Bounds.absBits,
  Library.Numerics.Bounds.finite, Library.Numerics.Bounds.nextUpBits,
  Library.Numerics.Bounds.nextDownBits, Library.Numerics.Bounds.endpoint,
  Library.Numerics.Interval.join, Library.Numerics.Interval.fmin, Library.Numerics.Interval.fmax,
  Library.Numerics.Interval.clamp, Demos.Sgp4.around, Demos.Sgp4.Omm.field,
  Demos.Sgp4.Omm.fieldNonneg]

end Demos.Sgp4.Omm
