import Library.Numerics.Float64.Log1p.Compiled
import TestSupport.Numerics.WorstCases
import TestSupport.Numerics.Reference

/-! A native check of `Library.Numerics.Float64.Log1p.log1p` against a reference computed with Lean's integers, rounded to
the nearest double.  fdlibm states an error below one unit in the last place, so each result must
lie within one unit of the reference.  The arguments are evenly spaced values from -1 to 10 and from
-0.3 to 0.42, the range without reduction, hashed positive values over all exponents, hashed values
from -1 to 0, the doubles next to the high words that the code compares with, next to the `x` at
which `1 + x` crosses the code's `√2` and `√2/2`, and next to `2 ^ 53`, the doubles `-1 + 2 ^ -k`,
and the special values.  Lean has no `log1p` that calls the C library, so the check reports no
library distance.  The arguments also include those of `WorstCases`, which give the largest known
errors of thirteen libraries in Tables 4 to 11 of the August 2026 report by Gladman, Innocente,
Mather, Ozaki, and Zimmermann.  It exits with an error at the first result further than one unit
from the reference.  Run with `lake env lean --run`. -/

namespace TestSupport.Numerics.Log1pAccuracy

open Verified.Examples Reference

/-- The double nearest to `log (1 + x)`.  From -1/4 to 1/4 it is `2 atanh (x/(2 + x))` from
`Reference.atanhFixed` at the precision of `x` plus 8 bits, where `x/(2 + x) = m/(2 ^ (1 - e) + m)`
for `x = m · 2 ^ e` and the argument is below `1/7` in magnitude.  The truncated quotient and the
series leave less than `4 n + 9` units for `n` terms, a relative error below `2 ^ -380`, since
`|log (1 + x)| ≥ 0.89 |x|` there.  Elsewhere it is `Reference.log` of the exact `1 + x` at
precision `P`, whose error of `2 ^ 13` units is below a relative `2 ^ -380`, since
`|log (1 + x)| ≥ 0.22` there. -/
def reference (x : Float) : Float :=
  if x.isNaN || x < -1.0 then Float.ofBits 0x7FF8000000000000
  else if x == -1.0 then Float.ofBits 0xFFF0000000000000
  else if x == 0.0 || x.isInf then x
  else
    let (m, e) := exactValue x
    if x.abs ≤ 0.25 then
      let q := precision x + 8
      let den := ((2 : Int) ^ (1 - e).toNat + m).toNat
      let a := 2 * atanhFixed (m.natAbs * 2 ^ q / den) q
      toFloat (if m < 0 then -(a : Int) else a) (-(q : Int))
    else
      let (mm, ee) : Nat × Int :=
        if e < 0 then ((m + 2 ^ (-e).toNat).toNat, e) else ((m * 2 ^ e.toNat + 1).toNat, 0)
      toFloat (Reference.log mm ee P) (-(P : Int))

def args : Array Float :=
  let thresholds : Array Float :=
    #[0x3FDA827A00000000, 0xBFD2BEC400000000, 0x3E20000000000000, 0xBE20000000000000,
      0x3C90000000000000, 0xBC90000000000000, 0x4340000000000000, 0xBFF0000000000000,
      0x7FEFFFFFFFFFFFFF, 0x0010000000000000, 0x8010000000000000].map Float.ofBits
  let crossings := #[Float.ofBits 0x3FF6A09E00000000 - 1.0, Float.ofBits 0x3FE6A09E00000000 - 1.0]
  let edges := (thresholds ++ crossings).flatMap near
  let toMinusOne := (Array.range 53).map fun k =>
    -1.0 + Float.ofBits ((1022 - UInt64.ofNat k) <<< 52)
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, -1.0, -2.0, -1e300, 1e300, 1e-300, -1e-300, Float.ofBits 1,
    Float.ofBits 0x8000000000000001]
  evenly 100000 (-1.0) 10.0 ++ evenly 100000 (-0.3) 0.42 ++
    (hashed 100000 41 0 2047).map Float.abs ++ (hashed 50000 43 0 1023).map (fun x => -x.abs) ++
    edges ++ toMinusOne ++ special ++
    WorstCases.log1p.map Float.ofBits

end TestSupport.Numerics.Log1pAccuracy

open Verified.Examples TestSupport.Numerics.Reference TestSupport.Numerics.Log1pAccuracy in
def main : IO UInt32 := do
  let mut ours : Tally := {}
  for x in args do
    let ref := reference x
    let y := Library.Numerics.Float64.Log1p.log1p x
    unless (distance y ref).any (· ≤ 1) do
      IO.eprintln s!"fail: log1p at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
      return 1
    ours := ours.add y ref
  IO.println s!"log1p accuracy: {args.size} results lie within {units ours.worst} of the \
    reference, {ours.unequal} of them unequal"
  return 0
