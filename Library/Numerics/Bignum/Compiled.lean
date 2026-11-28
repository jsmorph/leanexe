module

public import Library.Numerics.Bignum.Program
public import Library.Numerics.Bignum.Flat
public import Verified.Reflect.Command

@[expose] public section

/-! The verified compilation of the library.  The list starts with the reused functions of
MultiPrecision, Uscale, and Int64Text, each callee before its callers, and the helpers marked
`@[inline]` in the program, among them `natDivMod`, `intTDivMod`, and `intEDivMod`, are expanded
into their callers. -/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision Library.Numerics.Arithmetic.Uscale
open Library.Numerics.Decimal.Int64Text

verified_compile compiled := [width, Library.Numerics.MultiPrecision.add,
  Library.Numerics.MultiPrecision.sub, Library.Numerics.MultiPrecision.mul, significant,
  mulSmall, wordBits, shortDiv, tooBig, trial, longDiv, divide, limb, cmpStep,
  Library.Numerics.Arithmetic.Uscale.le, digitCount, digitByte, isDigitW,
  natTrim, natCmp, natAdd, natSub, natMul, natDivModChecked,
  intNeg, intCmp, intAdd, intSub, intMul, intTDivModChecked, intEDivModChecked,
  intToText, intOfText,
  textNeg, textCmp, textAdd, textSub, textMul, textTDiv, textTMod, textEDiv, textEMod]

end Library.Numerics.Bignum
