import Verified.Examples.Log
import Verified.Examples.Reference

/-! A native check of `Log.log` against `Reference.log` rounded to the nearest double.  Arm's
comments bound the error below one unit in the last place, so each result must lie within one unit
of the reference.  The check first compares each pair of table entries with the center `c` that
they describe: `chi + clo` with `1/invc` within `2 ^ -100` relatively, and `logc` with `log c`
within `2 ^ -66`, the bound that Arm's comment states.  The arguments are evenly spaced values from
0 to 20 and from 0.9 to 1.1, hashed positive values over all exponents, doubles on both sides of
1 at hashed distances of up to `2 ^ 36` units spread over 36 binades of distance, the doubles next
to the ends of the path near 1, next to 1, and at the ends of the binades and of the subnormals,
negative values, and the special values.  It also reports, for information, the distance from the
reference of the C library's `log`, which Lean's `Float.log` calls.  The check exits with an error
at the first result further than one unit from the reference.  Run with `lake env lean --run`. -/

namespace Verified.Examples.LogAccuracy

open Verified.Examples Reference

/-- The double nearest to `log x`. -/
def reference (x : Float) : Float :=
  if x.isNaN || x < 0.0 then Float.ofBits 0x7FF8000000000000
  else if x == 0.0 then Float.ofBits 0xFFF0000000000000
  else if x.isInf then x
  else
    let (m, e) := exactValue x
    toFloat (Reference.log m.toNat e P) (-(P : Int))

/-- Whether entry `i` of the tables describes one center `c`: `chi + clo` agrees with `1/invc`
within `2 ^ -100` relatively, and `logc` with `log (chi + clo)` within `2 ^ -66`. -/
def tableEntryOk (i : Nat) : Bool :=
  let (im, ie) := exactValue (Float.ofBits Log.logTable[2 * i]!)
  let (lm, le) := exactValue (Float.ofBits Log.logTable[2 * i + 1]!)
  let (hm, he) := exactValue (Float.ofBits Log.logTable2[2 * i]!)
  let (cm, ce) := exactValue (Float.ofBits Log.logTable2[2 * i + 1]!)
  -- `c · 2 ^ P`, exact, since `he + P` and `ce + P` are positive.
  let c := Reference.shift hm (he + P) + Reference.shift cm (ce + P)
  -- `c · invc · 2 ^ (2 P)`, exact.
  let product := c * Reference.shift im (ie + P)
  let inverseOk := (product - 2 ^ (2 * P)).natAbs * 2 ^ 100 ≤ 2 ^ (2 * P)
  let logOk := (Reference.shift lm (le + P) - Reference.log c.toNat (-(P : Int)) P).natAbs *
    2 ^ 66 ≤ 2 ^ P
  inverseOk && logOk

def args : Array Float :=
  let edges := #[Float.ofBits 0x3FEE000000000000, Float.ofBits 0x3FF1090000000000, 1.0, 0.5, 2.0,
    Float.ofBits 0x0010000000000000, Float.ofBits 0x000FFFFFFFFFFFFF, Float.ofBits 2,
    Float.ofBits 0x7FEFFFFFFFFFFFFF, Float.ofBits 0x3FE6000000000000,
    Float.ofBits 0x3FF6000000000000].flatMap near
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, Float.ofBits 1, -1.0, -1e-300, -1e300]
  let near1 := (Array.range 40000).map fun i =>
    let h := (UInt64.ofNat i + 37) * 0x9e3779b97f4a7c15
    let offset := (h >>> 28) >>> (h % 36)
    if h &&& 0x8000 == 0 then Float.ofBits (0x3FF0000000000000 + offset)
    else Float.ofBits (0x3FEFFFFFFFFFFFFF - offset)
  evenly 100000 0.0 20.0 ++ evenly 100000 0.9 1.1 ++ (hashed 100000 31 0 2047).map Float.abs ++
    near1 ++ edges ++ special

end Verified.Examples.LogAccuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.LogAccuracy in
def main : IO UInt32 := do
  unless (List.range 128).all tableEntryOk do
    IO.eprintln "fail: a table entry differs from its center"
    return 1
  let mut ours : Tally := {}
  let mut library : Tally := {}
  for x in args do
    let ref := reference x
    let y := Log.log x
    unless (distance y ref).any (· ≤ 1) do
      IO.eprintln s!"fail: log at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
      return 1
    ours := ours.add y ref
    library := library.add (Float.log x) ref
  IO.println s!"log accuracy: the tables agree with their centers, and {args.size} results lie \
    within {units ours.worst} of the reference, {ours.unequal} of them unequal"
  IO.println s!"log accuracy: the C library's results lie within {units library.worst} of the \
    reference, {library.unequal} of them unequal{library.unorderedNote}"
  return 0
