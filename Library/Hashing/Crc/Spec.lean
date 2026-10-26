import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ZMod.Defs

/-! CRC-32 and CRC-32C as polynomial remainders over GF(2), transcribed from ITU-T V.42 (03/2002)
§8.1.1.6.2 and §8.1.2, and from RFC 3720 §2.3.3 and §12.1.  A message is a string of bits, and
`poly` makes its first bit the highest coefficient.  V.42 §8.1.2.2 transmits bit 1 of each octet,
its lowest-order bit, first.  RFC 3720 §12.1 makes bit 7 of the lowest numbered byte, which §2.3.3
gives the value `2^0`, the highest coefficient, followed by bit 6, so both documents order each
octet's bits from the least significant.  The 32-bit frame check sequence of V.42 is the ones
complement of the sum of the remainders of `x^k L` and `x^32 M`, where `L` is `x^31 + … + 1`, and
`crc32` and `crc32c` give it with the generators of V.42 and RFC 3720.  `rfcProcess` transcribes
the process of RFC 3720 §12.1, which `rfcProcess_eq` shows gives the same sequence for at least 32
bits.

V.42 places the sequence's coefficient of `x^31` in bit 1 of the first octet of the field and its
coefficient of `x^0` in bit 8 of the fourth, and RFC 3720 places them in bit 7 of the lowest
numbered byte of the digest and bit 0 of the highest.  Neither defines an integer for the
sequence.  `value` gives the integer that zlib and other CRC code report, whose bit `i` is the
coefficient of `x^(31 - i)`.  The four octets, each read with its least significant bit as `2^0`,
are then the bytes of `value` from the least significant, the order in which gzip stores the CRC
by RFC 1952 §2.1. -/

namespace Library.Hashing.Crc.Spec

open Polynomial

/-- A string of bits in transmission order. -/
abbrev Bits := List Bool

/-- The polynomial whose coefficients are the bits of `M`, the first bit as the coefficient of
`x^(k - 1)` and the last as that of `x^0`, for a string of `k` bits. -/
noncomputable def poly : Bits → (ZMod 2)[X]
  | [] => 0
  | b :: M => (if b then X ^ M.length else 0) + poly M

/-- `x^31 + x^30 + … + x + 1`, the polynomial of 32 ones. -/
noncomputable def ones32 : (ZMod 2)[X] := poly (List.replicate 32 true)

/-- The generator of the 32-bit FCS of V.42 §8.1.1.6.2. -/
noncomputable def g32 : (ZMod 2)[X] :=
  X ^ 32 + X ^ 26 + X ^ 23 + X ^ 22 + X ^ 16 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 8 + X ^ 7 + X ^ 5 +
    X ^ 4 + X ^ 2 + X + 1

/-- The polynomial of a hexadecimal value in the notation of RFC 3720 §12.1: bit `i` of the value
is the coefficient of `x^i`, so that `0x3b` stands for `x^5 + x^4 + x^3 + x + 1`. -/
noncomputable def hexPoly (h : Nat) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range (h.log2 + 1), if h.testBit i then X ^ i else 0

/-- The generator `0x11edc6f41` of CRC32C in RFC 3720 §12.1. -/
noncomputable def g32c : (ZMod 2)[X] := hexPoly 0x11edc6f41

/-- The ones complement of a 32-bit sequence held as a polynomial of degree below 32: each of its
32 coefficients flipped, which over GF(2) adds `ones32`. -/
noncomputable def complement32 (R : (ZMod 2)[X]) : (ZMod 2)[X] := R + ones32

/-- The 32-bit FCS of V.42 §8.1.1.6.2 for the generator `G` and the `k` bits `M`: the ones
complement of the sum (modulo 2) of the remainder of `x^k L` divided by `G` and the remainder of
`x^32 M` divided by `G`. -/
noncomputable def fcs (G : (ZMod 2)[X]) (M : Bits) : (ZMod 2)[X] :=
  complement32 ((X ^ M.length * ones32) %ₘ G + (X ^ 32 * poly M) %ₘ G)

/-- The process of RFC 3720 §12.1 for a PDU `M` of at least 32 bits: complement the most
significant 32 bits, multiply by `x^32`, divide by `G`, and complement the remainder. -/
noncomputable def rfcProcess (G : (ZMod 2)[X]) (M : Bits) : (ZMod 2)[X] :=
  complement32 ((X ^ 32 * poly ((M.take 32).map not ++ M.drop 32)) %ₘ G)

/-- The bits of bytes, the least significant bit of each byte first.  V.42 §8.1.2.2 and §8.1.2.3
transmit bit 1 of an octet, its lowest-order bit, first, and RFC 3720 §12.1 takes bit 7, which
§2.3.3 gives the value `2^0`, as the highest coefficient. -/
def bitsOfBytes (bs : List UInt8) : Bits := bs.flatMap fun b => (List.range 8).map b.toNat.testBit

/-- A 32-bit sequence held as a polynomial of degree below 32, as the integer whose bit `i` is
its coefficient of `x^(31 - i)`. -/
noncomputable def value (R : (ZMod 2)[X]) : Nat :=
  ∑ i ∈ Finset.range 32, if R.coeff (31 - i) = 1 then 2 ^ i else 0

/-- CRC-32 of a string of bytes: the 32-bit FCS of V.42. -/
noncomputable def crc32 (bs : List UInt8) : Nat := value (fcs g32 (bitsOfBytes bs))

/-- CRC-32C of a string of bytes: the 32-bit FCS of V.42 with the generator of RFC 3720. -/
noncomputable def crc32c (bs : List UInt8) : Nat := value (fcs g32c (bitsOfBytes bs))

end Library.Hashing.Crc.Spec
