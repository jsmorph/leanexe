import Library.Numerics.Float64.Tgamma.Program
import TestSupport.Numerics.WorstCases
import TestSupport.Numerics.GammaReference

/-! A native check of `Library.Numerics.Float64.Tgamma.tgamma` against the reference of `GammaReference`, rounded to the
nearest double.  CORE-MATH's `tgamma` is correctly rounded, and the check requires one unit in the
last place, the decided bound, and reports how many results differ from the reference.  The
arguments are evenly spaced values from -185 to 172 and from -4 to 5, hashed values over the
exponents from `2 ^ -1074` to `2 ^ 7` with both signs, the integers from -200 to 172, the doubles
next to the integers from -190 to 172 and next to their halves, the doubles next to the code's
thresholds `2 ^ -112`, `1/4`, 3, 4, `0x1.573fae561f648p+7`, and -184, the 57 inputs of the table of
hard cases and the doubles next to them, the inputs of `WorstCases`, which give the largest known
errors of thirteen libraries in Tables 4 to 11 of the August 2026 report by Gladman, Innocente,
Mather, Ozaki, and Zimmermann, and the special values.  The check also calls `Library.Numerics.Float64.Tgamma.accurate`, the
path that the fast paths fall back on, at every eighth argument from -184 to 171 above `2 ^ -112` in
magnitude, other than the integers, and at the table's inputs, and requires the same bound of it.
It exits with an error at the first result further than one unit from the reference.  Run with
`lake env lean --run`. -/

namespace TestSupport.Numerics.TgammaAccuracy

open TestSupport.Numerics Reference GammaReference

def args : Array Float :=
  let integers := (Array.range 373).map fun i => (UInt64.ofNat i).toFloat - 200.0
  let nearIntegers := (Array.range 363).flatMap fun i =>
    let k := (UInt64.ofNat i).toFloat - 190.0
    near k ++ near (k + 0.5)
  let thresholds := #[Float.ofBits 0x38F0000000000000, 0.25, 3.0, 4.0,
    Float.ofBits 0x406573FAE561F648, -184.0].flatMap fun x => near x ++ near (-x)
  let table := (Array.range 57).flatMap fun k => near (Float.ofBits Library.Numerics.Float64.Tgamma.dbTable[3 * k]!)
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, Float.ofBits 1, Float.ofBits 0x8000000000000001,
    Float.ofBits 0x0004000000000000, Float.ofBits 0x8004000000000000, 0.5, -0.5, 1.0, 2.0]
  evenly 30000 (-185.0) 172.0 ++ evenly 20000 (-4.0) 5.0 ++ hashed 20000 71 0 1030 ++ integers ++
    nearIntegers ++ thresholds ++ table ++ WorstCases.tgamma.map Float.ofBits ++ special

end TestSupport.Numerics.TgammaAccuracy

open TestSupport.Numerics TestSupport.Numerics.Reference TestSupport.Numerics.GammaReference
  TestSupport.Numerics.TgammaAccuracy in
def main : IO UInt32 := do
  let mut ours : Tally := {}
  for x in args do
    let ref := tgammaReference x
    let y := Library.Numerics.Float64.Tgamma.tgamma x
    unless (distance y ref).any (· ≤ 1) do
      IO.eprintln s!"fail: tgamma at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
      return 1
    ours := ours.add y ref
  IO.println s!"tgamma accuracy: {args.size} results lie within {units ours.worst} of the \
    reference, {ours.unequal} of them unequal{ours.unorderedNote}"
  let slow := args.filter fun x =>
    -184.0 < x && x < 171.0 && x.abs ≥ Float.ofBits 0x38F0000000000000 && !negativeInteger x &&
      !(x > 0.0 && Library.Numerics.Float64.Tgamma.floorF x == x)
  let slow := ((Array.range (slow.size / 8)).map fun i => slow[8 * i]!) ++
    (Array.range 57).map fun k => Float.ofBits Library.Numerics.Float64.Tgamma.dbTable[3 * k]!
  let mut accurate : Tally := {}
  for x in slow do
    let ref := tgammaReference x
    let y := Library.Numerics.Float64.Tgamma.accurate Library.Numerics.Float64.Tgamma.accurateTable Library.Numerics.Float64.Tgamma.dbTable x
    unless (distance y ref).any (· ≤ 1) do
      IO.eprintln s!"fail: the accurate path at bits {x.toBits}: {y.toBits}, the reference \
        {ref.toBits}"
      return 1
    accurate := accurate.add y ref
  IO.println s!"tgamma accuracy: {slow.size} results of the accurate path lie within \
    {units accurate.worst} of the reference, {accurate.unequal} of them unequal"
  return 0
