import Verified.Examples.Asin
import Verified.Examples.ArcReference

/-! A native check of `Asin.asin` and `Asin.acos` against references computed with Lean's
integers through `ArcReference.asinFixed` and `ArcReference.acosFixed`, rounded to the nearest
double.  fdlibm states no error bound for either function, and the check requires one unit in the
last place, the largest distance it finds.  The arguments are evenly spaced values from -1 to 1,
hashed values over the exponents below 1 with both signs, the doubles `±(1 - 2 ^ -k)`, the doubles
next to the high words that the code compares with and to `±1`, and the special values.  The
check also reports, for information, the distance from the reference of the C library's `asin` and
`acos`, which Lean's `Float.asin` and `Float.acos` call.  It exits with an error at the first
result further than one unit from the reference.  Run with `lake env lean --run`. -/

namespace Verified.Examples.AsinAccuracy

open Verified.Examples Reference ArcReference

/-- The double nearest to `v · 2 ^ -q` with the sign `neg`. -/
def signed (neg : Bool) (v : Int) (q : Nat) : Float :=
  toFloat (if neg then -v else v) (-(q : Int))

/-- The double nearest to `asin x`, at the precision of `x` plus 8 bits, at which `|x|` scales to
an exact integer.  `asinFixed` errs by less than `2 ^ 15` units there, a relative error below
`2 ^ -390`, since `|asin x| ≥ |x|`. -/
def asinReference (x : Float) : Float :=
  if x.isNaN || x.abs > 1.0 then Float.ofBits 0x7FF8000000000000
  else if x == 0.0 then x
  else if x.abs == 1.0 then signed (x < 0.0) (pi (P + 1) / 4) P
  else
    let q := precision x + 8
    signed (x < 0.0) (asinFixed (scaled x.abs q).toNat q) q

/-- The double nearest to `acos x`, at precision 600, at which `x · 2 ^ 1200` is an exact integer.
`acosFixed` errs by less than `2 ^ 13` units there, a relative error below `2 ^ -560`, since
`acos x ≥ 2 ^ -27` for every double below 1. -/
def acosReference (x : Float) : Float :=
  if x.isNaN || x.abs > 1.0 then Float.ofBits 0x7FF8000000000000
  else if x == 1.0 then 0.0
  else if x == -1.0 then signed false (pi P) P
  else
    let (m, e) := exactValue x
    signed false (acosFixed (Reference.shift m (e + 1200)) 600) 600

def args : Array Float :=
  let thresholds : Array UInt64 :=
    #[0x3FE0000000000000, 0x3FEF333300000000, 0x3E50000000000000, 0x3C60000000000000,
      0x3FF0000000000000]
  let edges := (thresholds ++ thresholds.map (· ||| 0x8000000000000000)).flatMap
    fun b => near (Float.ofBits b)
  let toOne := (Array.range 53).flatMap fun k =>
    let v := 1.0 - Float.ofBits ((1022 - UInt64.ofNat k) <<< 52)
    #[v, -v]
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 2.0, -2.0, 1e-300, -1e-300, Float.ofBits 1,
    Float.ofBits 0x8000000000000001]
  evenly 100000 (-1.0) 1.0 ++ hashed 100000 71 0 1023 ++ toOne ++ edges ++ special

end Verified.Examples.AsinAccuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.AsinAccuracy in
def main : IO UInt32 := do
  let mut ours : Tally := {}
  let mut library : Tally := {}
  for x in args do
    for (name, y, l, ref) in [("asin", Asin.asin x, Float.asin x, asinReference x),
        ("acos", Asin.acos x, Float.acos x, acosReference x)] do
      unless (distance y ref).any (· ≤ 1) do
        IO.eprintln s!"fail: {name} at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
        return 1
      ours := ours.add y ref
      library := library.add l ref
  IO.println s!"asin accuracy: {2 * args.size} results of asin and acos lie within \
    {units ours.worst} of the reference, {ours.unequal} of them unequal"
  IO.println s!"asin accuracy: the C library's results lie within {units library.worst} of the \
    reference, {library.unequal} of them unequal{library.unorderedNote}"
  return 0
