module

public import Library.Numerics.Bignum.Third.Program
public import Library.Numerics.Bignum.Flat
public import Verified.Reflect.Command

@[expose] public section

/-! The verified compilation of the third iteration: the reused functions of MultiPrecision,
Uscale, and Int64Text, the first iteration's `natTrim`, `natAdd`, `natSub`, and `intToText`, the
second iteration's in-place helpers and its shift-carry Algorithm D, and the third iteration's
division and printer, each callee before its callers.  The helpers marked `@[inline]`, among them
`natDivModS`, `natDivModBZWith`, `natDivModBZ`, and `levelsFor`, are expanded into their
callers, so the divisions that follow Lean's convention at a zero divisor are not exported.  The declarations are in the namespace `Library.Numerics.Bignum.Third`, apart
from the earlier iterations' `compiled`. -/

namespace Library.Numerics.Bignum.Third

open Library.Numerics.Bignum
open Library.Numerics.MultiPrecision Library.Numerics.Arithmetic.Uscale
open Library.Numerics.Decimal.Int64Text

set_option maxHeartbeats 4000000 in
verified_compile compiled := [width, Library.Numerics.MultiPrecision.add,
  Library.Numerics.MultiPrecision.sub, significant, mulSmall, wordBits, shortDiv, tooBig, trial,
  limb, cmpStep, Library.Numerics.Arithmetic.Uscale.le, digitCount, digitByte,
  addGen, subGen, baseMul, kara, trimSeg, mulAddSeg, longDivS, divideS,
  natTrim, natAdd, natSub, intToText,
  trialAt, mulSubSeg, baseDiv, mulChunk, mulAcc, subFix, halfStep, lowHalf, rdiv, tdiv, udiv, divSmallSeg, divSeg,
  natDivModCheckedBZWith, natDivModCheckedBZ, signTDiv, signEDiv, intTDivModCheckedBZ,
  intEDivModCheckedBZ, leafChunks, powInit, toChunks, textOfChunks, chunksDC, natToTextDCWith, natToTextDC, intToTextDC]

end Library.Numerics.Bignum.Third
