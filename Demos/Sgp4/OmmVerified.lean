import Demos.Sgp4.Omm
import Verified.Reflect.Command
import Library.Numerics.Interval.Encoding

namespace Demos.Sgp4.Omm

open Library.Numerics.Bounds Library.Numerics.Decimal in
verified_compile compiled := [ParseFloat.limb, ParseFloat.mulSmall, ParseFloat.shl,
  ParseFloat.cmpStep, ParseFloat.le, ParseFloat.sub, ParseFloat.wordBits, ParseFloat.bitLen,
  ParseFloat.divStep, ParseFloat.divBits, ParseFloat.scaledQuot, ParseFloat.pow10Word,
  ParseFloat.mulPow10, ParseFloat.isDigitW, ParseFloat.isHexW, ParseFloat.hexValW,
  ParseFloat.lowerW, ParseFloat.span, ParseFloat.matchLower, ParseFloat.expDigits,
  ParseFloat.expPart, ParseFloat.digitPos, ParseFloat.leadingZeros, ParseFloat.anyNonzero,
  ParseFloat.chunkVal, ParseFloat.digitsVal, ParseFloat.hexVal, ParseFloat.roundUnits,
  ParseFloat.decRound, ParseFloat.decParse, ParseFloat.hexParse, ParseFloat.pow10Float,
  ParseFloat.fastPath, ParseFloat.parse64, absBits, finite, nextUpBits, nextDownBits, endpoint,
  Library.Numerics.Interval.join, Demos.Sgp4.around, field]

end Demos.Sgp4.Omm
