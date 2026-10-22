import Library.Numerics.Float64.Tan.Compiled
import TestSupport.Numerics.WorstCases
import TestSupport.Numerics.Reference

/-! A native check of `Library.Numerics.Float64.Tan.tan` against a reference computed with Lean's integers, rounded to the
nearest double.  fdlibm states that the result is nearly rounded, and the check requires one unit in
the last place.  The arguments are those of `TrigAccuracy.lean`: hashed values over the exponents
from `2 ^ -30` to `2 ^ 1023` with both signs, evenly spaced values up to 100, the doubles at and
next to the rounded `k · π/2` for `k` up to 20,000, where `tan` has its zeros and poles, and the
five hard arguments with their negatives.  To these the check adds the doubles next to the high
words that the code compares with and the special values.  The arguments also include those of
`WorstCases`, which give the largest known errors of thirteen libraries in Tables 4 to 11 of the
August 2026 report by Gladman, Innocente, Mather, Ozaki, and Zimmermann.  It also reports, for
information, the distance from the reference of the C library's `tan`, which Lean's `Float.tan`
calls.  It exits with an error at the first result further than one unit from the reference.  Run
with `lake env lean --run`. -/

namespace TestSupport.Numerics.TanAccuracy

open Verified.Examples Reference

/-- The double nearest to `tan x`, as the quotient of the sine and cosine of `Reference`.  Below 1
in magnitude they come from `sinCosFixed` at the precision of `x` plus 8 bits, where `|ρ| ≤ 1`, so
that each lies within `2 ^ 9` units, below a relative `2 ^ -390`, since `|sin x| ≥ 0.84 |x|` and
`cos x ≥ 0.54`.  From 1 on they come from `sinCos` at 300 bits, within `2 ^ 8` units, and each is
at least `2 ^ -61` in magnitude for every double, since no double lies closer than about
`2 ^ -61` to a multiple of `π/2`, so that each lies within a relative `2 ^ -231`.  The truncated
quotient adds less than a relative `2 ^ -238`. -/
def reference (x : Float) : Float :=
  if x.isNaN || x.isInf then Float.ofBits 0x7FF8000000000000
  else if x == 0.0 then x
  else
    let (q, s, c) : Nat × Int × Int :=
      if x.abs < 1.0 then
        let q := precision x + 8
        let (s, c) := sinCosFixed (scaled x q) q
        (q, s, c)
      else
        let (s, c) := sinCos x 300
        (300, s, c)
    let v : Int := (s.natAbs * 2 ^ q / c.natAbs : Nat)
    toFloat (if (s < 0) != (c < 0) then -v else v) (-(q : Int))

def args : Array Float :=
  let hashed := (Array.range 100000).map fun i =>
    let h := (UInt64.ofNat i + 7) * 0x9e3779b97f4a7c15
    let e : UInt64 := 993 + (h >>> (52 : UInt64)) % 1054
    let x := Float.ofBits ((e <<< 52) ||| (h &&& 0xFFFFFFFFFFFFF))
    if h &&& 0x8000 == 0 then x else -x
  let even := (Array.range 20001).map fun i => (UInt64.ofNat i).toFloat * 0.005
  let multiples := (Array.range 20000).flatMap fun k =>
    let b := ((UInt64.ofNat (k + 1)).toFloat * 1.5707963267948966).toBits
    #[b - 1, b, b + 1].map Float.ofBits
  let hard : Array Float :=
    #[Float.ofBits (((1872 : UInt64) <<< (52 : UInt64)) ||| (6381956970095103 - 4503599627370496)),
      1647100.0, 1e22, 1e300, Float.ofBits 0x7FEFFFFFFFFFFFFF]
  let thresholds : Array UInt64 := #[0x3FE5942800000000, 0x3FE921FB00000000, 0x3E40000000000000]
  let edges := (thresholds ++ thresholds.map (· ||| 0x8000000000000000)).flatMap
    fun b => near (Float.ofBits b)
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 1e-300, -1e-300, Float.ofBits 1,
    Float.ofBits 0x8000000000000001]
  hashed ++ even ++ multiples ++ hard ++ hard.map (- ·) ++ edges ++ special ++
    WorstCases.tan.map Float.ofBits

end TestSupport.Numerics.TanAccuracy

open Verified.Examples TestSupport.Numerics.Reference TestSupport.Numerics.TanAccuracy in
def main : IO UInt32 := do
  let mut ours : Tally := {}
  let mut library : Tally := {}
  for x in args do
    let ref := reference x
    let y := Library.Numerics.Float64.Tan.tan x
    unless (distance y ref).any (· ≤ 1) do
      IO.eprintln s!"fail: tan at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
      return 1
    ours := ours.add y ref
    library := library.add (Float.tan x) ref
  IO.println s!"tan accuracy: {args.size} results lie within {units ours.worst} of the \
    reference, {ours.unequal} of them unequal"
  IO.println s!"tan accuracy: the C library's results lie within {units library.worst} of the \
    reference, {library.unequal} of them unequal{library.unorderedNote}"
  return 0
