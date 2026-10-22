import Library.Numerics.Float64.Lgamma.Program
import TestSupport.Numerics.WorstCases
import TestSupport.Numerics.GammaReference

/-! A native check of `Library.Numerics.Float64.Lgamma.lgammaR` against the reference of `GammaReference`, rounded to the
nearest double.  CORE-MATH's `lgamma` is correctly rounded, and the check requires one unit in the
last place, the decided bound, and reports how many results differ from the reference.  It also
requires the sign of `Γ x` as the second result for a finite `x` other than 0 and the negative
integers, and at those and the special values the signs that `Lgamma`'s docstring lists.  The
arguments are evenly spaced values from -20 to 20 and from 0.5 to 8.3, hashed values over all
exponents with both signs, the doubles next to the integers from -30 to 30 and to their halves, next
to the zeros of `lgamma` at 1 and 2 and to the 17 centers of the accurate path's polynomials near
the negative zeros, next to the borders of the 19 pieces and the code's thresholds, the 19 inputs of
the table of hard cases and the doubles next to them, the inputs of `WorstCases`, which give the
largest known errors of thirteen libraries in Tables 4 to 11 of the August 2026 report by Gladman,
Innocente, Mather, Ozaki, and Zimmermann, and the special values.  The check also calls
`Library.Numerics.Float64.Lgamma.accurate`, the path that the fast path falls back on, at every eighth finite argument other
than 0, the integers below 3, and the magnitudes from `0x1.754d9278b51a6p+1014` up, where
`cr_lgamma` returns before it, and at the table's inputs, and requires the same bound of it.  It
exits with an error at the first result that fails.  Run with `lake env lean --run`. -/

namespace TestSupport.Numerics.LgammaAccuracy

open TestSupport.Numerics Reference GammaReference

/-- The sign of `Γ x` that `lgammaR` returns. -/
def signReference (x : Float) : Float :=
  if x.isNaN || x.isInf then 1.0
  else if x == 0.0 then (if x.toBits >>> 63 == 1 then -1.0 else 1.0)
  else if negativeInteger x then
    if x.toBits <<< 1 ≥ 0xFEAEA9B24F16A34C then 1.0 else -1.0
  else if (lgammaFixed x Q).2 > 0 then 1.0 else -1.0

def args : Array Float :=
  let integers := (Array.range 61).flatMap fun i =>
    let k := (UInt64.ofNat i).toFloat - 30.0
    near k ++ near (k + 0.5)
  let centers : Array Nat :=
    #[128, 183, 240, 283, 326, 377, 418, 459, 510, 561, 614, 665, 722, 779, 838, 897, 954]
  let centers := centers.map fun o => -(Float.ofBits Library.Numerics.Float64.Lgamma.accurateTable[o]!)
  let zeros := (#[1.0, 2.0] ++ centers).flatMap near
  let borders := (Array.range 20).flatMap fun j =>
    near (Float.ofBits (Library.Numerics.Float64.Lgamma.mainTable[j]! <<< (37 : UInt64)))
  let thresholds := #[Float.ofBits 0x3B40000000000000, 0.03125, 0.5,
    Float.ofBits 0x4330000000000000, Float.ofBits 0x7F5754C000000000,
    Float.ofBits 0x4630000000000000, Float.ofBits 0x4770000000000000,
    Float.ofBits 0x39B0000000000000, Float.ofBits 0x7F5754D9278B51A6,
    Float.ofBits 0x7F5754D9278B51A7, Float.ofBits 0x7F5754D9278B51A6].flatMap fun x =>
      near x ++ near (-x)
  let table := (Array.range 19).flatMap fun k => near (Float.ofBits Library.Numerics.Float64.Lgamma.dbTable[3 * k]!)
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, Float.ofBits 1, Float.ofBits 0x8000000000000001,
    Float.ofBits 0x7FEFFFFFFFFFFFFF, Float.ofBits 0xFFEFFFFFFFFFFFFF,
    Float.ofBits 0xC330000000000000, 1.0, 2.0, -1.0, -2.0, 3.0]
  evenly 30000 (-20.0) 20.0 ++ evenly 20000 0.5 8.3 ++ hashed 30000 73 0 2047 ++ integers ++
    zeros ++ borders ++ thresholds ++ table ++ WorstCases.lgamma.map Float.ofBits ++ special

end TestSupport.Numerics.LgammaAccuracy

open TestSupport.Numerics TestSupport.Numerics.Reference TestSupport.Numerics.GammaReference
  TestSupport.Numerics.LgammaAccuracy in
def main : IO UInt32 := do
  let mut ours : Tally := {}
  for x in args do
    let ref := lgammaReference x
    let (y, s) := Library.Numerics.Float64.Lgamma.lgammaR x
    unless (distance y ref).any (· ≤ 1) do
      IO.eprintln s!"fail: lgamma at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
      return 1
    unless s.toBits == (signReference x).toBits do
      IO.eprintln s!"fail: the sign of lgammaR at bits {x.toBits}: {s}"
      return 1
    ours := ours.add y ref
  IO.println s!"lgamma accuracy: {args.size} results lie within {units ours.worst} of the \
    reference, {ours.unequal} of them unequal{ours.unorderedNote}, with their signs"
  let slow := args.filter fun x =>
    !x.isNaN && !x.isInf && x != 0.0 && !(Library.Numerics.Float64.Tgamma.floorF x == x && x < 3.0) &&
      x.toBits <<< 1 < 0xFEAEA9B24F16A34C
  let slow := ((Array.range (slow.size / 8)).map fun i => slow[8 * i]!) ++
    (Array.range 19).map fun k => Float.ofBits Library.Numerics.Float64.Lgamma.dbTable[3 * k]!
  let mut accurate : Tally := {}
  for x in slow do
    let ref := lgammaReference x
    let y := Library.Numerics.Float64.Lgamma.accurate Library.Numerics.Float64.Tgamma.logdTable Library.Numerics.Float64.Lgamma.logAccurateTable Library.Numerics.Float64.Lgamma.sinpiTable
      Library.Numerics.Float64.Lgamma.asymTable Library.Numerics.Float64.Lgamma.accurateTable Library.Numerics.Float64.Lgamma.dbTable x
    unless (distance y ref).any (· ≤ 1) do
      IO.eprintln s!"fail: the accurate path at bits {x.toBits}: {y.toBits}, the reference \
        {ref.toBits}"
      return 1
    accurate := accurate.add y ref
  IO.println s!"lgamma accuracy: {slow.size} results of the accurate path lie within \
    {units accurate.worst} of the reference, {accurate.unequal} of them unequal"
  return 0
