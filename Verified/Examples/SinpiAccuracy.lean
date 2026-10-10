import Verified.Examples.Sinpi
import Verified.Examples.Reference

/-! A native check of `Sinpi.sinpi`, `Sinpi.cospi`, and `Sinpi.tanpi` against references computed
with Lean's integers through `Reference.sinCosTurns`, rounded to the nearest double.  Kargl states
no error bound, and the check requires one unit in the last place, the largest distance it finds.
Where the result is a zero or an infinity, the check also requires its sign, by the rules of IEEE
754's `sinPi`, `cosPi`, and `tanPi`, which the sources follow: `sinpi n` has the sign of `n`,
`cospi (n + 1/2)` is `+0`, `tanpi n` has the sign of `n` for an even `n` and the other sign for an
odd one, and `tanpi (n + 1/2)` is `+∞` for an even `n` and `-∞` for an odd one.  The arguments are
evenly spaced values from -4 to 4, the multiples of `1/4` from -100 to 100 and the doubles next to
them, where the functions have their zeros, poles, and values `±1`, the doubles next to
`n + 1/2` for `n` up to `2 ^ 51`, hashed values over the exponents from `2 ^ -60` to `2 ^ 60` with
both signs, the doubles next to the high words that the code compares with, subnormal values, and
the special values.  Lean has no binding of these functions, so the check reports no library
distance.  It exits with an error at the first result that fails.  Run with
`lake env lean --run`. -/

namespace Verified.Examples.SinpiAccuracy

open Verified.Examples Reference

/-- For a finite `x`: whether `|x|` is an integer, whether it is an integer plus `1/2`, and the
integer part of `|x|`. -/
def kind (x : Float) : Bool × Bool × Nat :=
  let (m, e) := exactValue x
  let a := m.natAbs
  if e ≥ 0 then (true, false, a * 2 ^ e.toNat)
  else
    let d := 2 ^ (-e).toNat
    if a % d == 0 then (true, false, a / d)
    else if 2 * a % d == 0 then (false, true, a / d)
    else (false, false, 0)

/-- `(sin (π |x|), cos (π |x|)) · 2 ^ q` from `Reference.sinCosTurns` at `|x|/2` turns, with `q`
the precision of `x` plus 64 bits.  Each value lies within `2 n + 4` units for `n` terms, at most
`2 ^ 10`.  From `1/4` on, a double lies at least `2 ^ -54` from each multiple of `1/2` that it is
not, so that `sin` and `cos` away from their exact zeros are at least `π · 2 ^ -54` in magnitude.
Below `1/4`, `cos` exceeds 0.7 and `sin (π x)` is near `π x`, which the precision of `x` covers.
The error therefore stays below a relative `2 ^ -390`. -/
def sinCosPi (x : Float) : Nat × Int × Int :=
  let (m, e) := exactValue x
  let (num, den) : Nat × Nat :=
    if e ≥ 1 then (m.natAbs * 2 ^ (e - 1).toNat, 1) else (m.natAbs, 2 ^ (1 - e).toNat)
  let q := precision x + 64
  let (s, c) := sinCosTurns num den q
  (q, s, c)

def nan : Float := Float.ofBits 0x7FF8000000000000

def sinpiReference (x : Float) : Float :=
  if x.isNaN || x.isInf then nan
  else
    let (isInt, _, _) := kind x
    let neg := x.toBits >>> 63 == 1
    if isInt then if neg then -0.0 else 0.0
    else
      let (q, s, _) := sinCosPi x
      toFloat (if neg then -s else s) (-(q : Int))

def cospiReference (x : Float) : Float :=
  if x.isNaN || x.isInf then nan
  else
    let (_, isHalf, _) := kind x
    if isHalf then 0.0
    else
      let (q, _, c) := sinCosPi x
      toFloat c (-(q : Int))

def tanpiReference (x : Float) : Float :=
  if x.isNaN || x.isInf then nan
  else
    let (isInt, isHalf, n) := kind x
    let neg := x.toBits >>> 63 == 1
    if isInt then if neg != (n % 2 == 1) then -0.0 else 0.0
    else if isHalf then
      if (n % 2 == 0) != neg then Float.ofBits 0x7FF0000000000000
      else Float.ofBits 0xFFF0000000000000
    else
      let (q, s, c) := sinCosPi x
      let v : Int := (s.natAbs * 2 ^ q / c.natAbs : Nat)
      let quotientNeg := decide (s < 0) != decide (c < 0)
      toFloat (if quotientNeg != neg then -v else v) (-(q : Int))

/-- Whether `y` passes against `ref`: within one unit, and with the same bits where `ref` is a
zero or an infinity. -/
def passes (y ref : Float) : Bool :=
  (distance y ref).any (· ≤ 1) && (!(ref == 0.0 || ref.isInf) || y.toBits == ref.toBits)

/-- `x` and `-x` for each `x`. -/
def both (xs : Array Float) : Array Float := xs.flatMap fun x => #[x, -x]

def args : Array Float :=
  let quarters := (Array.range 801).map fun i => (UInt64.ofNat i).toFloat * 0.25 - 100.0
  let halves := both ((Array.range 52).map fun k =>
    Float.ofBits ((UInt64.ofNat (1023 + k)) <<< 52) + 0.5)
  let thresholds : Array UInt64 :=
    #[0x3E20000000000000, 0x3FD0000000000000, 0x3FE0000000000000, 0x3FE8000000000000,
      0x3FF0000000000000, 0x4330000000000000, 0x4340000000000000]
  let edges := both (thresholds.map Float.ofBits)
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 1e300, -1e300, 1e-300, -1e-300, Float.ofBits 1,
    Float.ofBits 0x8000000000000001, Float.ofBits 0x000FFFFFFFFFFFFF,
    Float.ofBits 0x7FEFFFFFFFFFFFFF]
  evenly 100000 (-4.0) 4.0 ++ quarters.flatMap near ++ halves.flatMap near ++
    hashed 100000 139 963 120 ++ edges.flatMap near ++ special

end Verified.Examples.SinpiAccuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.SinpiAccuracy in
def main : IO UInt32 := do
  for (name, f, reference) in
      [("sinpi", Sinpi.sinpi, sinpiReference), ("cospi", Sinpi.cospi, cospiReference),
       ("tanpi", Sinpi.tanpi, tanpiReference)] do
    let mut ours : Tally := {}
    for x in args do
      let ref := reference x
      let y := f x
      unless passes y ref do
        IO.eprintln s!"fail: {name} at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
        return 1
      ours := ours.add y ref
    IO.println s!"sinpi accuracy: {args.size} results of {name} lie within {units ours.worst} of \
      the reference, {ours.unequal} of them unequal, with the signs of the zeros and infinities"
  return 0
