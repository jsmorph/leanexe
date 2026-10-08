import Verified.Reflect.Command

/-! The sixth program of the verified compiler: pairs as parameters and results, built with
`(a, b)` and taken apart with `.1`, `.2`, and `match`, a pair inside a pair, and calls that pass
and return pairs.  A pair is carried as the words of its components, so a function with a pair
result returns several WebAssembly results. -/

namespace Verified.Examples.Pairs

def divMod (a b : UInt64) : UInt64 × UInt64 := (a / b, a % b)

def swapAdd (p : UInt64 × UInt64) : UInt64 × UInt64 := (p.2, p.1 + p.2)

def sumPair (p : UInt64 × UInt64) : UInt64 := let (x, y) := p; x + y

def minMax (a b : UInt64) : UInt64 × UInt64 := if a ≤ b then (a, b) else (b, a)

def spread (a b c : UInt64) : UInt64 :=
  let (lo, hi) := minMax a b
  let (q, r) := divMod hi (c ||| 1)
  hi - lo + q * r + sumPair (swapAdd (q, r))

def nested (a b : UInt64) : (UInt64 × Bool) × UInt64 := ((a + b, a == b), a ^^^ b)

def unnest (p : (UInt64 × Bool) × UInt64) : UInt64 := if p.1.2 then p.1.1 else p.2

/-- A triple, which the patterns below take apart. -/
def triple (a : UInt64) : UInt64 × UInt64 × UInt64 := (a, a + 1, a * 3)

/-- A pattern that takes a call's triple apart. -/
def sumTriple (a : UInt64) : UInt64 := let (x, y, z) := triple a; x + y * z

/-- A pattern nested on the left, on a pair built in place. -/
def leftNested (a b : UInt64) : UInt64 := let ((x, y), z) := ((a, b), a ^^^ b); x * y + z

/-- A pattern with a wildcard. -/
def skipMiddle (a : UInt64) : UInt64 := let (x, _, z) := triple a; x + z

/-- A pattern that keeps a pair whole. -/
def keepPair (a : UInt64) : UInt64 := let (x, yz) := triple a; x + yz.1 - yz.2

/-- A pair built in place whose second component the body uses twice, which is computed once. -/
def literalTwice (a b : UInt64) : UInt64 := let (x, y) := (a, b * b + 1); x + y * y

/-- A pattern that takes apart a call inside a pair built in place, which is computed once. -/
def literalCall (a b : UInt64) : UInt64 := let (x, y, z) := (a, swapAdd (b, a)); x + y * z

/-- A triple that holds arrays. -/
def splitArrays (xs : Array UInt64) : UInt64 × Array UInt64 × Array UInt64 :=
  (xs.size.toUInt64, xs.push 1, xs.push 2)

/-- A pattern that takes apart a triple that holds arrays. -/
def sizesOf (xs : Array UInt64) : UInt64 :=
  let (n, ys, zs) := splitArrays xs
  n + ys.size.toUInt64 * 10 + zs.size.toUInt64 * 100

verified_compile compiled := [divMod, swapAdd, sumPair, minMax, spread, nested, unnest, triple,
  sumTriple, leftNested, skipMiddle, keepPair, literalTwice, literalCall, splitArrays, sizesOf]

end Verified.Examples.Pairs
