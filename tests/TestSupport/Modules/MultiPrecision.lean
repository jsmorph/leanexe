import Library.Numerics.MultiPrecision.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of multiple-precision arithmetic. -/

namespace Library.Numerics.MultiPrecision

open TestSupport.Host

/-- `len` arbitrary digits: bits 32 to 63 of the 64-bit product, modulo `2^64`, of two arbitrary
words, so that consecutive digits do not differ by a fixed amount. -/
def arbitraryDigits (len seed : Nat) : List UInt64 :=
  (List.range len).map fun i => (rw (seed + i) * rw (seed + 7 * i + 3)) >>> 32

/-- The pairs of the verified compiler's cases, each run by addition, subtraction, and
multiplication.  The short pairs are two empty numbers, an empty number with a nonempty one of one
and of three digits in both orders and of two digits after it, equal numbers, a carry out of one
digit and out of a run of the largest digit `2^32 - 1`, a borrow through a run of zero digits, a
borrow at digit 0 through a digit where both arguments agree, differences whose first argument is
the smaller, a longer argument with high zero digits in both positions, equal values of different
lengths, zero numbers of several lengths, products of the largest digits, and the digit `2^31`
doubled, alone and above a zero digit.  The arbitrary pairs have every pair
of lengths from 1 to 8 digits.  The long pairs have 60 and 45 arbitrary digits, 100 and 1, 1 and
100, 150 and 120, a run of 60 largest digits plus 1, two runs of 50 largest digits, and 30 largest
digits above 30 zeros with 20 zeros above 20 largest digits. -/
def mpInputs : List (List UInt64 × List UInt64) :=
  let top : UInt64 := 4294967295
  let chosen : List (List UInt64 × List UInt64) :=
    [([], []), ([0], []), ([], [5]), ([5, 7], []), ([], [3, 4, 5]), ([3, 4, 5], []), ([1], [1]),
      ([top], [1]), ([top, top, top], [1]), ([1], [top, top, top]), ([top, top], [top, top]),
      ([0, 0, 1], [1]), ([5], [7]), ([1, 2, 3], [3, 2, 1]), ([2], [1, 0, 0]), ([1, 0, 0], [2]),
      ([1, 0], [1]), ([0], [0, 0, 0]), ([0, 0], [0]), ([top, top, top, top], [top, top]),
      ([2147483648], [2]), ([0, 2147483648], [0, 2])]
  let arbitrary := (List.range 64).map fun k =>
    (arbitraryDigits (k / 8 + 1) (100 * k), arbitraryDigits (k % 8 + 1) (100 * k + 50))
  let long : List (List UInt64 × List UInt64) :=
    [(arbitraryDigits 60 7000, arbitraryDigits 45 8000), (arbitraryDigits 100 9000, [rw 77 >>> 32]),
      ([rw 78 >>> 32], arbitraryDigits 100 9500),
      (arbitraryDigits 150 12000, arbitraryDigits 120 13000),
      (List.replicate 60 top, [1]), (List.replicate 50 top, List.replicate 50 top),
      (List.replicate 30 0 ++ List.replicate 30 top, List.replicate 20 top ++ List.replicate 20 0)]
  chosen ++ arbitrary ++ long

end Library.Numerics.MultiPrecision
