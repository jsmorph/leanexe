module

public import Demos.BignumCalc.MessageProgram
public import Library.Numerics.Bignum.Flat
public import Verified.Reflect.Command

@[expose] public section

/-! The verified compilation of the calculator of the bare-metal program and the AArch64 Image.  It
is a separate compilation, so that `compiled`, the WebAssembly module of the call theorems and the
program of the C form, keeps its functions and bytes.  The list holds the functions that the
calculator reaches, in the order of `compiled`'s list without the three exports of division with a
status, followed by `calcLine`, `unpack`, `pack`, `calcWords`, function 44, and `calcBytes`,
function 45. -/

namespace Demos.BignumCalc

open Library.Numerics.Bignum

open Library.Numerics.MultiPrecision Library.Numerics.Arithmetic.Uscale
open Library.Numerics.Decimal.Int64Text

verified_compile messageCompiled := [width, Library.Numerics.MultiPrecision.add,
  Library.Numerics.MultiPrecision.sub, Library.Numerics.MultiPrecision.mul, significant,
  mulSmall, wordBits, shortDiv, tooBig, trial, longDiv, divide, limb, cmpStep,
  Library.Numerics.Arithmetic.Uscale.le, digitCount, digitByte, isDigitW,
  natTrim, natCmp, natAdd, natSub, natMul,
  intNeg, intCmp, intAdd, intSub, intMul,
  intToText, intOfText,
  textNeg, textCmp, textAdd, textSub, textMul, textTDiv, textTMod, textEDiv, textEMod,
  calcLine, unpack, pack, calcWords, calcBytes]

end Demos.BignumCalc
