import Verified.Examples.Sinh
import Verified.Examples.WorstCases
import Verified.Examples.HyperbolicReference

/-! A native check of `Sinh.sinh` and `Sinh.cosh` against references computed with Lean's integers
through `HyperbolicReference.sinhFixed` and `coshFixed`, rounded to the nearest double.  fdlibm
states no error bound for either function, and the check requires the largest distance it finds: two
units in the last place for `sinh` and one for `cosh`.  The arguments are evenly spaced values from
-30 to 30 and from 709 to 711 with both signs, around fdlibm's thresholds near `ln (DBL_MAX)` and
the overflow threshold, hashed values over the exponents from `2 ^ -60` to `2 ^ 9` with both signs,
the doubles next to the high words that the code compares with, and the special values.  The
arguments also include those of `WorstCases`, which give the largest known errors of thirteen
libraries in Tables 4 to 11 of the August 2026 report by Gladman, Innocente, Mather, Ozaki, and
Zimmermann.  The check also reports, for information, the distance from the reference of the C
library's `sinh` and `cosh`, which Lean's `Float.sinh` and `Float.cosh` call.  It exits with an
error at the first result further from the reference than its bound.  Run with
`lake env lean --run`. -/

namespace Verified.Examples.SinhAccuracy

open Verified.Examples Reference HyperbolicReference

/-- The double nearest to `sinh x`, at the precision of `x` plus 8 bits, below a relative
`2 ^ -390`.  From 1100 on in magnitude the result overflows. -/
def sinhReference (x : Float) : Float :=
  if x.isNaN || x.isInf || x == 0.0 then x
  else if x.abs ≥ 1100.0 then if x < 0.0 then Float.ofBits 0xFFF0000000000000
    else Float.ofBits 0x7FF0000000000000
  else
    let q := precision x + 8
    let v := sinhFixed (scaled x.abs q).toNat q
    toFloat (if x < 0.0 then -v else v) (-(q : Int))

/-- The double nearest to `cosh x`, at precision `P`, below a relative `2 ^ -380`.  From 1100 on
in magnitude the result overflows. -/
def coshReference (x : Float) : Float :=
  if x.isNaN then x
  else if x.isInf || x.abs ≥ 1100.0 then Float.ofBits 0x7FF0000000000000
  else if x == 0.0 then 1.0
  else toFloat (coshFixed (scaled x.abs P).toNat P) (-(P : Int))

def args : Array Float :=
  let thresholds : Array UInt64 :=
    #[0x4036000000000000, 0x3E30000000000000, 0x3FF0000000000000, 0x40862E4200000000,
      0x408633CE00000000, 0x3FD62E4300000000, 0x3C80000000000000]
  let edges := (thresholds ++ thresholds.map (· ||| 0x8000000000000000)).flatMap
    fun b => near (Float.ofBits b)
  let overflow := evenly 4000 709.0 711.0
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 1e300, -1e300, 1e-300, -1e-300, Float.ofBits 1,
    Float.ofBits 0x8000000000000001, Float.ofBits 0x7FEFFFFFFFFFFFFF]
  evenly 100000 (-30.0) 30.0 ++ overflow ++ overflow.map (- ·) ++ hashed 100000 79 963 70 ++
    edges ++ special ++
    (WorstCases.sinh ++ WorstCases.cosh).map Float.ofBits

end Verified.Examples.SinhAccuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.SinhAccuracy in
def main : IO UInt32 := do
  let mut sinhs : Tally := {}
  let mut coshs : Tally := {}
  let mut sinhLib : Tally := {}
  let mut coshLib : Tally := {}
  for x in args do
    let rs := sinhReference x
    let ys := Sinh.sinh x
    unless (distance ys rs).any (· ≤ 2) do
      IO.eprintln s!"fail: sinh at bits {x.toBits}: {ys.toBits}, the reference {rs.toBits}"
      return 1
    let rc := coshReference x
    let yc := Sinh.cosh x
    unless (distance yc rc).any (· ≤ 1) do
      IO.eprintln s!"fail: cosh at bits {x.toBits}: {yc.toBits}, the reference {rc.toBits}"
      return 1
    sinhs := sinhs.add ys rs
    coshs := coshs.add yc rc
    sinhLib := sinhLib.add (Float.sinh x) rs
    coshLib := coshLib.add (Float.cosh x) rc
  IO.println s!"sinh accuracy: {args.size} results of sinh lie within {units sinhs.worst} of the \
    reference, {sinhs.unequal} of them unequal, and {args.size} of cosh within \
    {units coshs.worst}, {coshs.unequal} unequal"
  IO.println s!"sinh accuracy: the C library's sinh lies within {units sinhLib.worst} of the \
    reference, {sinhLib.unequal} unequal{sinhLib.unorderedNote}, and its cosh within \
    {units coshLib.worst}, {coshLib.unequal} unequal{coshLib.unorderedNote}"
  return 0
