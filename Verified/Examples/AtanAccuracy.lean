import Verified.Examples.Atan
import Verified.Examples.WorstCases
import Verified.Examples.ArcReference

/-! A native check of `Atan.atan` and `Atan.atan2` against references computed with Lean's integers
through `ArcReference.atanQuotient`, rounded to the nearest double.  fdlibm states no error bound
for either function, and the check requires the largest distance it finds: one unit in the last
place for `atan` and two for `atan2`.  The arguments of `atan` are evenly spaced values from -10 to
10, hashed values over all exponents with both signs, the doubles next to the high words that the
code compares with, and the special values.  The pairs `(y, x)` of `atan2` are hashed pairs over all
exponents, hashed pairs whose exponents differ by 55 to 65 in both directions, around the code's
limits of `2 ^ 60` and `2 ^ -60` on `|y/x|`, with all four signs, hashed `y` with `x = 1`, and every
pair of special values.  The arguments also include those of `WorstCases`, which give the largest
known errors of thirteen libraries in Tables 4 to 11 of the August 2026 report by Gladman,
Innocente, Mather, Ozaki, and Zimmermann.  The check also reports, for information, the distance
from the reference of the C library's `atan` and `atan2`, which Lean's `Float.atan` and
`Float.atan2` call.  It exits with an error at the first result further from the reference than its
bound.  Run with `lake env lean --run`. -/

namespace Verified.Examples.AtanAccuracy

open Verified.Examples Reference ArcReference

/-- The double nearest to `v · 2 ^ -q` with the sign `neg`. -/
def signed (neg : Bool) (v : Int) (q : Nat) : Float :=
  toFloat (if neg then -v else v) (-(q : Int))

/-- The double nearest to `atan x`, at the precision of `x` plus 8 bits below 1 in magnitude and
at `P` above, where the result exceeds `π/4`.  `atanQuotient` errs by less than `2 ^ 14` units at
these precisions, a relative error below `2 ^ -390`. -/
def atanReference (x : Float) : Float :=
  if x.isNaN || x == 0.0 then x
  else if x.isInf then signed (x < 0.0) (pi (P + 1) / 4) P
  else
    let (m, e) := exactValue x
    let q := if x.abs < 1.0 then precision x + 8 else P
    let (num, den) : Nat × Nat :=
      if e ≥ 0 then (m.natAbs * 2 ^ e.toNat, 1) else (m.natAbs, 2 ^ (-e).toNat)
    signed (m < 0) (atanQuotient num den q) q

/-- The double nearest to `atan2 y x`, with IEEE 754's results for zeros, infinities, and NaN.
For finite nonzero arguments, `|y|/|x| = num/den` exactly.  For a positive `x` the precision is
`P` plus 8 bits plus the binary orders of magnitude by which `|y/x|` falls below 1, so that the
`2 ^ 14` units of `atanQuotient` stay below a relative `2 ^ -390`.  At that precision, which may
exceed `W - 15`, `num ≤ den`, so `atanQuotient` uses no `π`.  For a negative `x` the result
exceeds `π/2` in magnitude and the precision is `P`. -/
def atan2Reference (y x : Float) : Float :=
  if x.isNaN || y.isNaN then Float.ofBits 0x7FF8000000000000
  else
    let yneg := y.toBits >>> 63 == 1
    let xneg := x.toBits >>> 63 == 1
    if y == 0.0 then if xneg then signed yneg (pi P) P else y
    else if x == 0.0 then signed yneg (pi (P + 1) / 4) P
    else if x.isInf then
      if y.isInf then signed yneg (if xneg then 3 * pi P / 4 else pi P / 4) P
      else if xneg then signed yneg (pi P) P
      else if yneg then -0.0 else 0.0
    else if y.isInf then signed yneg (pi (P + 1) / 4) P
    else
      let (my, ey) := exactValue y
      let (mx, ex) := exactValue x
      let lo := min ey ex
      let num := my.natAbs * 2 ^ (ey - lo).toNat
      let den := mx.natAbs * 2 ^ (ex - lo).toNat
      let q := if xneg then P else P + (Nat.log2 den - Nat.log2 num) + 8
      let a := atanQuotient num den q
      signed yneg (if xneg then pi q - a else a) q

def atanArgs : Array Float :=
  let thresholds : Array UInt64 :=
    #[0x4410000000000000, 0x3FDC000000000000, 0x3E40000000000000, 0x3FF3000000000000,
      0x3FE6000000000000, 0x4003800000000000]
  let edges := (thresholds ++ thresholds.map (· ||| 0x8000000000000000)).flatMap
    fun b => near (Float.ofBits b)
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 1.0, -1.0, 1e300, -1e300, 1e-300, -1e-300, Float.ofBits 1,
    Float.ofBits 0x8000000000000001, Float.ofBits 0x7FEFFFFFFFFFFFFF]
  evenly 100000 (-10.0) 10.0 ++ hashed 100000 51 0 2047 ++ edges ++ special ++
    WorstCases.atan.map Float.ofBits

def atan2Args : Array (Float × Float) :=
  let ys := hashed 60000 53 0 2047
  let xs := hashed 60000 59 0 2047
  let pairs := (Array.range 60000).map fun i => (ys[i]!, xs[i]!)
  -- `y = x · 2 ^ d` with a hashed fraction for `|d|` from 55 to 65 and all four signs.
  let far := (Array.range 22000).map fun i =>
    let h := (UInt64.ofNat i + 61) * 0x9e3779b97f4a7c15
    let d : UInt64 := (55 : UInt64) + (h >>> 59) % 11
    let x := Float.ofBits ((((900 : UInt64) + (h >>> 40) % 200) <<< 52) ||| (h &&& 0xFFFFFFFFFFFFF))
    let fraction := Float.ofBits ((0x3FF0000000000000 : UInt64) ||| ((h >>> 20) &&& 0xFFFFF))
    let y := Float.ofBits (if h &&& 0x10000 == 0 then x.toBits + (d <<< 52)
      else x.toBits - (d <<< 52)) * fraction
    let x := if h &&& 0x8000 == 0 then x else -x
    let y := if h &&& 0x4000 == 0 then y else -y
    (y, x)
  let ones := (hashed 2000 67 900 250).map fun y => (y, 1.0)
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 1.0, -1.0, 2.5, -2.5, 1e-300, -1e-300, Float.ofBits 1,
    Float.ofBits 0x7FEFFFFFFFFFFFFF]
  let worst := WorstCases.atan2.flatMap fun (y, x) =>
    #[(Float.ofBits y, Float.ofBits x), (Float.ofBits x, Float.ofBits y)]
  pairs ++ far ++ ones ++ worst ++ special.flatMap fun y => special.map fun x => (y, x)

end Verified.Examples.AtanAccuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.AtanAccuracy in
def main : IO UInt32 := do
  let mut ours : Tally := {}
  let mut library : Tally := {}
  for x in atanArgs do
    let ref := atanReference x
    let y := Atan.atan x
    unless (distance y ref).any (· ≤ 1) do
      IO.eprintln s!"fail: atan at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
      return 1
    ours := ours.add y ref
    library := library.add (Float.atan x) ref
  IO.println s!"atan accuracy: {atanArgs.size} results of atan lie within {units ours.worst} of \
    the reference, {ours.unequal} of them unequal"
  IO.println s!"atan accuracy: the C library's results lie within {units library.worst} of the \
    reference, {library.unequal} of them unequal{library.unorderedNote}"
  let mut ours2 : Tally := {}
  let mut library2 : Tally := {}
  for (y, x) in atan2Args do
    let ref := atan2Reference y x
    let r := Atan.atan2 y x
    unless (distance r ref).any (· ≤ 2) do
      IO.eprintln s!"fail: atan2 at bits {y.toBits} {x.toBits}: {r.toBits}, the reference \
        {ref.toBits}"
      return 1
    ours2 := ours2.add r ref
    library2 := library2.add (Float.atan2 y x) ref
  IO.println s!"atan accuracy: {atan2Args.size} results of atan2 lie within {units ours2.worst} \
    of the reference, {ours2.unequal} of them unequal"
  IO.println s!"atan accuracy: the C library's atan2 results lie within \
    {units library2.worst} of the reference, {library2.unequal} of them \
    unequal{library2.unorderedNote}"
  return 0
