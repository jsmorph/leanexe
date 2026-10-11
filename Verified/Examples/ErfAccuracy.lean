import Verified.Examples.Erf
import Verified.Examples.WorstCases
import Verified.Examples.ErfReference

/-! A native check of `Erf.erf` and `Erf.erfc` against references computed with Lean's integers
through `ErfReference`, rounded to the nearest double.  fdlibm states an error below one unit in the
last place for `erf` below 0.84375 and nothing elsewhere, and the check requires the largest
distances it finds: one unit in the last place for `erf` and four for `erfc`, which it reaches at
`0x1.527f4fb0d9331p+0`, Musl's input in Table 7.  The arguments are evenly spaced values from -7 to
7 and from 6 to 28, hashed values over the exponents from `2 ^ -60` to `2 ^ 6` with both signs, the
doubles next to the high words that the code compares with, the doubles from 27.2 to 27.3, where
`erfc` enters the subnormal range, and the special values.  Lean has no binding of the C library's
`erf` and `erfc`, so the check reports no library distance.  The arguments also include those of
`WorstCases`, which give the largest known errors of thirteen libraries in Tables 4 to 11 of the
August 2026 report by Gladman, Innocente, Mather, Ozaki, and Zimmermann.  It exits with an error at
the first result further from the reference than its bound.  Run with `lake env lean --run`. -/

namespace Verified.Examples.ErfAccuracy

open Verified.Examples Reference ErfReference

/-- The double nearest to `erf x`: below 6 in magnitude `x · erfFactor` at precision `P`, within a
relative `2 ^ -393`, and `±1` from 6 on, where `erfc x < erfc 6 < 2 ^ -54` puts `1 - erfc x` above
the midpoint `1 - 2 ^ -54` between 1 and the double below it. -/
def erfReference (x : Float) : Float :=
  if x.isNaN || x == 0.0 then x
  else if x.isInf || x.abs ≥ 6.0 then if x < 0.0 then -1.0 else 1.0
  else
    let (m, e) := exactValue x.abs
    let v := m * erfFactor m.toNat e P
    toFloat (if x < 0.0 then -v else v) (e - P)

/-- The double nearest to `erfc x`.  Below 6 in magnitude it is `1 ∓ erf |x|` at precision `P`,
within a relative `2 ^ -330`, since `erfc x > 2 ^ -56` there.  From 6 to 28 it is
`e^(-x²) K/√π` from `Reference.exp`, `erfcFraction`, and `sqrtPi`, within a relative `2 ^ -385`.
From 28 on it is 0, since `erfc 28 < 2 ^ -1131`, and from -6 down it is 2, since
`2 - erfc 6` lies above the midpoint `2 - 2 ^ -53` between 2 and the double below it. -/
def erfcReference (x : Float) : Float :=
  if x.isNaN then x
  else if x == 0.0 then 1.0
  else if x.isInf then if x < 0.0 then 2.0 else 0.0
  else if x ≤ -6.0 then 2.0
  else if x ≥ 28.0 then 0.0
  else
    let (m, e) := exactValue x.abs
    if x.abs < 6.0 then
      let erf := Reference.shift (m * erfFactor m.toNat e P) e
      toFloat (if x < 0.0 then 2 ^ P + erf else 2 ^ P - erf) (-(P : Int))
    else
      let (v, k) := exp (-(Reference.shift (m * m) (2 * e + P))) P
      toFloat (v * erfcFraction m.toNat e P / sqrtPi P) k

/-- `x` and `-x` for each `x`. -/
def both (xs : Array Float) : Array Float := xs.flatMap fun x => #[x, -x]

def args : Array Float :=
  let thresholds : Array UInt64 :=
    #[0x3FEB000000000000, 0x3E30000000000000, 0x0080000000000000, 0x3FF4000000000000,
      0x4018000000000000, 0x4006DB6E00000000, 0x4006DB6D00000000, 0x3C70000000000000,
      0x3FD0000000000000, 0x403C000000000000]
  let edges := both (thresholds.map Float.ofBits) |>.flatMap near
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 1.0, -1.0, 1e300, -1e300, 1e-300, -1e-300, Float.ofBits 1,
    Float.ofBits 0x8000000000000001, Float.ofBits 0x7FEFFFFFFFFFFFFF]
  evenly 100000 (-7.0) 7.0 ++ evenly 20000 6.0 28.0 ++ hashed 100000 137 963 67 ++ edges ++
    evenly 2000 27.2 27.3 ++ special ++
    (WorstCases.erf ++ WorstCases.erfc).map Float.ofBits

end Verified.Examples.ErfAccuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.ErfAccuracy in
def main : IO UInt32 := do
  for (name, bound, f, reference) in
      [("erf", 1, Erf.erf, erfReference), ("erfc", 4, Erf.erfc, erfcReference)] do
    let mut ours : Tally := {}
    for x in args do
      let ref := reference x
      let y := f x
      unless (distance y ref).any (· ≤ bound) do
        IO.eprintln s!"fail: {name} at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
        return 1
      ours := ours.add y ref
    IO.println s!"erf accuracy: {args.size} results of {name} lie within {units ours.worst} of \
      the reference, {ours.unequal} of them unequal"
  return 0
