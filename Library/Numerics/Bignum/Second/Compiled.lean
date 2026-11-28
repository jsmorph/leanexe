module

public import Library.Numerics.Bignum.Second.Program
public import Library.Numerics.Bignum.Flat
public import Verified.Reflect.Command

@[expose] public section

/-! The verified compilation of the second iteration: the in-place helpers, Karatsuba's product
and its callers, and the reader by divide and conquer, each callee before its callers.  Int64Text's
`isDigitW` is the one reused function; the helpers marked `@[inline]`, `mulLong`, `chunkValue`,
and the first iteration's `allDigits`, are expanded into their callers.  The declarations are in
the namespace `Library.Numerics.Bignum.Second`, apart from the first iteration's `compiled`. -/

namespace Library.Numerics.Bignum.Second

open Library.Numerics.Bignum
open Library.Numerics.Decimal.Int64Text (isDigitW)

set_option maxHeartbeats 1000000 in
verified_compile compiled := [isDigitW, addGen, subGen, baseMul, kara, trimSeg,
  natMulKaraWith, natMulKara, intMulKara, mulAddSeg, readInit, readPass, decimalValueDC,
  natOfTextDCWith, natOfTextDC, intOfTextDC]

end Library.Numerics.Bignum.Second
