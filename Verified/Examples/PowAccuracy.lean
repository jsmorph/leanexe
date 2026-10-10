import Verified.Examples.Pow
import Verified.Examples.WorstCases
import Verified.Examples.PowerReference

/-! A native check of `Pow.pow` against a reference computed with Lean's integers through
`PowerReference.powExponent` and `Reference.exp`, rounded to the nearest double, with the special
cases of C99's Annex F.  Arm states a worst-case error of 0.54 units in the last place, so each
result must lie within one unit of the reference.  The pairs `(x, y)` are hashed pairs with `x` from
`2 ^ -60` to `2 ^ 60` and `y` from `2 ^ -10` to `2 ^ 10` in magnitude, `x` within `2 ^ 20` units of
1 with `|y|` from `2 ^ 20` to `2 ^ 50`, negative `x` with the integers `y` from -100 to 100, `x = 2`
and `x = -2` with the integers and halves `y` from -1080 to 1030, `x = 10` and `x = 0.1` with `y`
near the limits of overflow and underflow, and every pair of the special values.  The arguments also
include those of `WorstCases`, which give the largest known errors of thirteen libraries in Tables 4
to 11 of the August 2026 report by Gladman, Innocente, Mather, Ozaki, and Zimmermann.  It also
reports, for information, the distance from the reference of the C library's `pow`, which Lean's
`Float.pow` calls.  It exits with an error at the first result further than one unit from the
reference.  Run with `lake env lean --run`. -/

namespace Verified.Examples.PowAccuracy

open Verified.Examples Reference

/-- Whether the finite `y = m · 2 ^ e` is an integer, and whether it is an odd one. -/
def integerKind (y : Float) : Bool × Bool :=
  let (m, e) := exactValue y
  if e ≥ 0 then (true, e == 0 && m.natAbs % 2 == 1)
  else
    let d := 2 ^ (-e).toNat
    if m.natAbs % d != 0 then (false, false) else (true, m.natAbs / d % 2 == 1)

/-- The double nearest to `x ^ y`.  The special cases are those of C99's Annex F (F.10.4.4).  For a
finite nonzero `x`, finite `y`, and a negative `x` only with an integer `y`, `|x| ^ y` is
`exp (y log |x|)` from `PowerReference.powExponent` at precision 500, which lies within
`|y| · 2 ^ 13 + 1` units, and `Reference.exp`, with the sign of `x` for an odd `y`.  From 1100 in
magnitude on, the exponent gives an infinity or a zero, with that sign.  Below that,
`|y| < 1100 · 2 ^ 53`, since `|log x| ≥ 2 ^ -53` for every double other than 1, so that the
exponent's error and that of `Reference.exp` leave a relative error below `2 ^ -420`. -/
def reference (x y : Float) : Float :=
  let nan := Float.ofBits 0x7FF8000000000000
  let inf := Float.ofBits 0x7FF0000000000000
  if y == 0.0 || x == 1.0 then 1.0
  else if x.isNaN || y.isNaN then nan
  else if y.isInf then
    if x == -1.0 then 1.0
    else if x.abs < 1.0 then (if y > 0.0 then 0.0 else inf)
    else (if y > 0.0 then inf else 0.0)
  else
    let (isInt, isOdd) := integerKind y
    let negX := x.toBits >>> 63 == 1
    if x == 0.0 then
      if y < 0.0 then (if isOdd && negX then -inf else inf)
      else (if isOdd then x else 0.0)
    else if x.isInf then
      if !negX then (if y < 0.0 then 0.0 else inf)
      else if isOdd then (if y < 0.0 then -0.0 else -inf)
      else (if y < 0.0 then 0.0 else inf)
    else if negX && !isInt then nan
    else
      let neg := negX && isOdd
      let (mx, ex) := exactValue x.abs
      let (my, ey) := exactValue y
      let z := PowerReference.powExponent mx.toNat ex my ey
      let limit : Int := 1100 * 2 ^ 500
      if z ≥ limit then (if neg then -inf else inf)
      else if z ≤ -limit then (if neg then -0.0 else 0.0)
      else
        let (v, s) := exp z 500
        toFloat (if neg then -v else v) s

/-- `count` hashed doubles with biased exponents from `lo` to `lo + span - 1`, of the sign `neg`. -/
def hashedSigned (count : Nat) (seed lo span : UInt64) (neg : Bool) : Array Float :=
  (hashed count seed lo span).map fun x => if neg then -x.abs else x.abs

def pairs : Array (Float × Float) :=
  let xs := hashedSigned 60000 109 963 120 false
  let ys := hashed 60000 113 1013 20
  let ordinary := (Array.range 60000).map fun i => (xs[i]!, ys[i]!)
  let nearOne := (Array.range 20000).map fun i =>
    let h := (UInt64.ofNat i + 127) * 0x9e3779b97f4a7c15
    let below : UInt64 := 0x3FF0000000000000 - 0x100000
    let x := Float.ofBits (below + (h >>> (43 : UInt64)))
    let e : UInt64 := (1043 : UInt64) + (h >>> (20 : UInt64)) % 31
    let y := Float.ofBits ((e <<< 52) ||| (h &&& 0xFFFFFFFFFFFFF))
    (x, if h &&& 0x8000 == 0 then y else -y)
  let negative := (Array.range 20000).map fun i =>
    let h := (UInt64.ofNat i + 131) * 0x9e3779b97f4a7c15
    let e : UInt64 := (1015 : UInt64) + (h >>> (59 : UInt64)) % 16
    let x := -(Float.ofBits ((e <<< 52) ||| (h &&& 0xFFFFFFFFFFFFF)))
    (x, (UInt64.ofNat ((h >>> 20).toNat % 201)).toFloat - 100.0)
  let twos := (Array.range 2111).flatMap fun i =>
    let k := (UInt64.ofNat i).toFloat - 1080.0
    #[(2.0, k), (2.0, k + 0.5), (-2.0, k)]
  let limits := (evenly 2000 300.0 310.0).map (fun y => (10.0, y)) ++
    (evenly 2000 300.0 330.0).map (fun y => (0.1, y))
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 1.0, -1.0, 0.5, -0.5, 2.0, -2.0, 3.0, -3.0, 2.5, -2.5, 1e300,
    -1e300, 1e-300, Float.ofBits 1, Float.ofBits 0x8000000000000001,
    Float.ofBits 0x7FEFFFFFFFFFFFFF, Float.ofBits 0x3B90000000000000,
    Float.ofBits 0x43F0000000000000, Float.ofBits 0xC3F0000000000000]
  let worst := WorstCases.pow.map fun (x, y) => (Float.ofBits x, Float.ofBits y)
  ordinary ++ nearOne ++ negative ++ twos ++ limits ++ worst ++
    special.flatMap fun x => special.map fun y => (x, y)

end Verified.Examples.PowAccuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.PowAccuracy in
def main : IO UInt32 := do
  let mut ours : Tally := {}
  let mut library : Tally := {}
  for (x, y) in pairs do
    let ref := reference x y
    let r := Pow.pow x y
    unless (distance r ref).any (· ≤ 1) do
      IO.eprintln s!"fail: pow at bits {x.toBits} {y.toBits}: {r.toBits}, the reference \
        {ref.toBits}"
      return 1
    ours := ours.add r ref
    library := library.add (Float.pow x y) ref
  IO.println s!"pow accuracy: {pairs.size} results lie within {units ours.worst} of the \
    reference, {ours.unequal} of them unequal"
  IO.println s!"pow accuracy: the C library's results lie within {units library.worst} of the \
    reference, {library.unequal} unequal{library.unorderedNote}"
  return 0
