/-! The specification of multiple-precision arithmetic.  A number is an array of digits in base
`2^32`, least significant first, each held in a word.  `value u` is the number, and `digits n x` is
the array of the `n` least significant digits of `x`, so it holds `x` modulo `2^(32 n)`.  The empty
array has the value 0, and zero digits at the top count toward a number's length.  `Digits u`
states that every word of `u` is below `2^32`.  The functions return arrays for every argument, and
the proofs assume `Digits` of both arguments, with fewer than `2^64` words in each, fewer than
`2^64` in both together for a product, and fewer than `2^62` in both together for a division, so
the results on other arrays carry no meaning.  The call theorems obtain the bound on each argument
from its array in memory, and those of the product and the division assume the bound on both
together.
Each result has a length fixed by the lengths of the arguments: `k + 1` digits for a sum and `k`
for a difference, where `k` is the larger length, so that a difference `u - v` with `u < v` is
`u - v + 2^(32 k)`, `m + n` digits for a product, where `m` and `n` are the lengths of `u` and `v`,
and for a division `m` digits of the quotient followed by `n` of the remainder.  Division by 0 gives
the quotient 0 and the remainder `u`, since Lean's `Nat` division sets `u / 0 = 0` and
`u % 0 = u`, and the remainder's `n` digits are the least significant digits of `u`, padded with
zero digits when `n > m`. -/

namespace Library.Numerics.MultiPrecision

/-- The base of the digits. -/
def base : Nat := 2 ^ 32

/-- The number that the first `q` digits of `u` represent: the sum of `u[i] * base ^ i` for
`i < q`. -/
def prefixValue (u : Array UInt64) (q : Nat) : Nat :=
  ((List.range q).map fun i => u[i]!.toNat * base ^ i).sum

/-- The number that the digits of `u` represent. -/
def value (u : Array UInt64) : Nat := prefixValue u u.size

/-- The `n` least significant digits of `x`. -/
def digits (n x : Nat) : Array UInt64 :=
  (Array.range n).map fun i => UInt64.ofNat (x / base ^ i % base)

/-- Every word of `u` is a digit. -/
def Digits (u : Array UInt64) : Prop := ∀ i, i < u.size → u[i]!.toNat < base

def addSpec (x : Array UInt64 × Array UInt64) : Array UInt64 :=
  digits (max x.1.size x.2.size + 1) (value x.1 + value x.2)

def subSpec (x : Array UInt64 × Array UInt64) : Array UInt64 :=
  digits (max x.1.size x.2.size) (value x.1 + base ^ max x.1.size x.2.size - value x.2)

def mulSpec (x : Array UInt64 × Array UInt64) : Array UInt64 :=
  digits (x.1.size + x.2.size) (value x.1 * value x.2)

def divSpec (x : Array UInt64 × Array UInt64) : Array UInt64 :=
  digits x.1.size (value x.1 / value x.2) ++ digits x.2.size (value x.1 % value x.2)

end Library.Numerics.MultiPrecision
