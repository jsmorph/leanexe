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

verified_compile compiled := [divMod, swapAdd, sumPair, minMax, spread, nested, unnest]

end Verified.Examples.Pairs
