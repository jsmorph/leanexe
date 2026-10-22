import Library.Numerics.Float64.Erfc.Compiled
import TestSupport.Numerics.WorstCases
import TestSupport.Numerics.ErfReference

/-! A native check of `Library.Numerics.Float64.Erfc.erfc`, the port of CORE-MATH's `erfc`, against the reference of
`ErfReference` rounded to the nearest double.  CORE-MATH's `erfc` is correctly rounded, and the
check requires every result to equal the reference.  The arguments are those of `ErfAccuracy`:
evenly spaced values from -7 to 7 and from 6 to 28, hashed values over the exponents from `2 ^ -60`
to `2 ^ 6` with both signs, the doubles from 27.2 to 27.3, and the special values, with the doubles
next to the thresholds of CORE-MATH's code in place of fdlibm's: the bounds of the special ranges,
the ends of the paths, the multiples of `1/16` and `1/8` that end the intervals of the polynomials
of `erf`, the reciprocals of the bounds of the intervals of `1/x`, and the 69 inputs of the hard
cases.  They also include the inputs of `WorstCases`, which give the largest known errors of
thirteen libraries in Tables 4 to 11 of the August 2026 report by Gladman, Innocente, Mather, Ozaki,
and Zimmermann.  The check also calls `Library.Numerics.Float64.Erfc.erfcAccurate`, the path that the fast path falls back
on, at every eighth argument in its range and at the inputs of the hard cases, and requires the
same.  It exits with an error at the first result unequal to the reference.  Run with
`lake env lean --run`. -/

namespace TestSupport.Numerics.ErfcAccuracy

open Verified.Examples Reference ErfReference

/-- The double nearest to `erfc x`.  Below 6 in magnitude it is
`1 ∓ erf |x|` at precision `P`, within a relative `2 ^ -330`, since `erfc x > 2 ^ -56` there.  From
6 to 28 it is `e^(-x²) K/√π` from `Reference.exp`, `erfcFraction`, and `sqrtPi`, within a relative
`2 ^ -385`.  From 28 on it is 0, since `erfc 28 < 2 ^ -1131`, and from -6 down it is 2, since
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

/-- The inputs of the 68 rows of the tables of hard cases and the subnormal case. -/
def hardInputs : Array Float :=
  ((Array.range 68).map fun k => Float.ofBits Library.Numerics.Float64.Erfc.excTable[3 * k]!) ++
    #[Float.ofBits 0x403A8F7BFBD15495]

def args : Array Float :=
  let thresholds : Array UInt64 :=
    #[0x4017744F8F74E94B, 0x3C9C5BF891B4EF6A, 0x3C8C5BF891B4EF6A, 0x403B39DC41E48BFD,
      0x400713786D9C7C09, 0x3FDE861FBB24C00A, 0x4039DB1BB14E15CA, 0x403A8B12FC6E4892,
      0x3FFB59FFB450828C, 0x3C40000000000000]
  let reciprocals : Array Float :=
    (#[0x3FBD500000000000, 0x3FC59DA6CA291BA6, 0x3FCBC00000000000, 0x3FD0C00000000000,
      0x3FD3800000000000, 0x3FD6300000000000, 0x3FB4500000000000, 0x3FBE000000000000,
      0x3FC3F00000000000, 0x3FC9500000000000, 0x3FCF500000000000, 0x3FD3100000000000,
      0x3FD7100000000000, 0x3FDBC00000000000, 0x3FE0B00000000000, 0x3FE3000000000000] :
      Array UInt64).map fun b => 1.0 / Float.ofBits b
  let sixteenths := (Array.range 96).map fun i => (UInt64.ofNat (i + 1)).toFloat / 16.0
  let edges := (both (thresholds.map Float.ofBits) ++ both reciprocals ++ both sixteenths).flatMap
    near
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 1.0, -1.0, 1e300, -1e300, 1e-300, -1e-300, Float.ofBits 1,
    Float.ofBits 0x8000000000000001, Float.ofBits 0x7FEFFFFFFFFFFFFF]
  evenly 100000 (-7.0) 7.0 ++ evenly 20000 6.0 28.0 ++ hashed 100000 137 963 67 ++ edges ++
    evenly 2000 27.2 27.3 ++ special ++ hardInputs.flatMap near ++
    WorstCases.erfc.map Float.ofBits

end TestSupport.Numerics.ErfcAccuracy

open Verified.Examples TestSupport.Numerics.Reference TestSupport.Numerics.ErfcAccuracy in
def main : IO UInt32 := do
  let mut ours : Tally := {}
  for x in args do
    let ref := erfcReference x
    let y := Library.Numerics.Float64.Erfc.erfc x
    unless (distance y ref).any (· == 0) do
      IO.eprintln s!"fail: erfc at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
      return 1
    ours := ours.add y ref
  IO.println s!"erfc accuracy: {args.size} results lie within {units ours.worst} of the \
    reference, {ours.unequal} of them unequal{ours.unorderedNote}"
  let slow := args.filter fun x =>
    x.isFinite && Float.ofBits 0xC017744F8F74E94B < x && x < Float.ofBits 0x403B39DC41E48BFD &&
      !(Float.ofBits 0xBC9C5BF891B4EF6A ≤ x && x ≤ Float.ofBits 0x3C8C5BF891B4EF6A)
  let slow := ((Array.range (slow.size / 8)).map fun i => slow[8 * i]!) ++ hardInputs
  let mut accurate : Tally := {}
  for x in slow do
    let ref := erfcReference x
    let y := Library.Numerics.Float64.Erfc.erfcAccurate Library.Numerics.Float64.Erfc.accTable Library.Numerics.Float64.Erfc.expAccTable Library.Numerics.Float64.Erfc.asymAccTable Library.Numerics.Float64.Erfc.excTable x
    unless (distance y ref).any (· == 0) do
      IO.eprintln s!"fail: the accurate path of erfc at bits {x.toBits}: {y.toBits}, the \
        reference {ref.toBits}"
      return 1
    accurate := accurate.add y ref
  IO.println s!"erfc accuracy: {slow.size} results of the accurate path lie within \
    {units accurate.worst} of the reference, {accurate.unequal} of them unequal"
  return 0
