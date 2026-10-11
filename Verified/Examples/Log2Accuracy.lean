import Verified.Examples.Log2
import Verified.Examples.WorstCases
import Verified.Examples.Log10
import Verified.Examples.PowerReference

/-! A native check of `Log2.log2` and `Log10.log10` against references computed with Lean's integers
through `PowerReference.log2` and `PowerReference.log10`, rounded to the nearest double.  Arm states
0.55 units in the last place for `log2` and `k_log.h` below one unit for fdlibm's logarithms, so
each result must lie within one unit of the reference.  The check first compares each pair of
`log2`'s table entries with the center `c` that they describe: `chi + clo` with `1/invc` within
`2 ^ -100` relatively, and `logc` with `log2 c` within `2 ^ -68`, the bound that Arm's comment
states.  The arguments are those of `LogAccuracy.lean`: evenly spaced values from 0 to 20 and from
0.9 to 1.1, hashed positive values over all exponents, doubles on both sides of 1 at hashed
distances of up to `2 ^ 36` units, the doubles next to the ends of the binades and of the
subnormals, negative values, and the special values.  To these the check adds the doubles next to
the ends of `log2`'s path near 1, the powers of 2, and the powers of 10 up to `10 ^ 22`, whose
logarithms are integers.  The arguments also include those of `WorstCases`, which give the largest
known errors of thirteen libraries in Tables 4 to 11 of the August 2026 report by Gladman,
Innocente, Mather, Ozaki, and Zimmermann.  It also reports, for information, the distance from the
reference of the C library's `log2` and `log10`, which Lean's `Float.log2` and `Float.log10` call.
It exits with an error at the first result further than one unit from the reference.  Run with
`lake env lean --run`. -/

namespace Verified.Examples.Log2Accuracy

open Verified.Examples Reference

/-- The double nearest to `log2 x` or `log10 x`, as `base` gives it, at precision 500, within
`2 ^ 14` units, a relative error below `2 ^ -420`, since `|log x|` is at least `2 ^ -53` for every
double other than 1.  0 gives `-∞`, a negative number NaN, and 1 gives 0. -/
def reference (base : Nat → Int → Nat → Int) (x : Float) : Float :=
  if x.isNaN || x < 0.0 then Float.ofBits 0x7FF8000000000000
  else if x == 0.0 then Float.ofBits 0xFFF0000000000000
  else if x.isInf then x
  else if x == 1.0 then 0.0
  else
    let (m, e) := exactValue x
    toFloat (base m.toNat e 500) (-500)

/-- Whether entry `i` of the tables of `log2` describes one center `c`: `chi + clo` agrees with
`1/invc` within `2 ^ -100` relatively, and `logc` with `log2 (chi + clo)` within `2 ^ -68`. -/
def tableEntryOk (i : Nat) : Bool :=
  let (im, ie) := exactValue (Float.ofBits Log2.log2Table[2 * i]!)
  let (lm, le) := exactValue (Float.ofBits Log2.log2Table[2 * i + 1]!)
  let (hm, he) := exactValue (Float.ofBits Log2.log2Table2[2 * i]!)
  let (cm, ce) := exactValue (Float.ofBits Log2.log2Table2[2 * i + 1]!)
  -- `c · 2 ^ 500`, exact, since `he + 500` and `ce + 500` are positive.
  let c := Reference.shift hm (he + 500) + Reference.shift cm (ce + 500)
  -- `c · invc · 2 ^ 1000`, exact.
  let product := c * Reference.shift im (ie + 500)
  let inverseOk := (product - 2 ^ 1000).natAbs * 2 ^ 100 ≤ 2 ^ 1000
  let logc := Reference.shift lm (le + 500)
  let logOk := (logc - PowerReference.log2 c.toNat (-500) 500).natAbs * 2 ^ 68 ≤ 2 ^ 500
  inverseOk && logOk

def args : Array Float :=
  let edges := #[Float.ofBits 0x3FEEA4AF00000000, Float.ofBits 0x3FF0B55900000000, 1.0, 0.5, 2.0,
    Float.ofBits 0x0010000000000000, Float.ofBits 0x000FFFFFFFFFFFFF, Float.ofBits 2,
    Float.ofBits 0x7FEFFFFFFFFFFFFF, Float.ofBits 0x3FE6000000000000,
    Float.ofBits 0x3FF6000000000000, Float.ofBits 0x3FF6A09E00000000,
    Float.ofBits 0x3FE6A09E00000000].flatMap near
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, Float.ofBits 1, -1.0, -1e-300, -1e300]
  let near1 := (Array.range 40000).map fun i =>
    let h := (UInt64.ofNat i + 37) * 0x9e3779b97f4a7c15
    let offset := (h >>> 28) >>> (h % 36)
    if h &&& 0x8000 == 0 then Float.ofBits (0x3FF0000000000000 + offset)
    else Float.ofBits (0x3FEFFFFFFFFFFFFF - offset)
  let subnormalTwos := (Array.range 52).map fun k => Float.ofBits ((1 : UInt64) <<< UInt64.ofNat k)
  let powersOf2 := (Array.range 2046).map fun k => Float.ofBits ((UInt64.ofNat (k + 1)) <<< 52)
  let powersOf10 := (Array.range 23).map fun k => Float.ofNat (10 ^ k)
  evenly 100000 0.0 20.0 ++ evenly 100000 0.9 1.1 ++ (hashed 100000 107 0 2047).map Float.abs ++
    near1 ++ edges ++ subnormalTwos ++ powersOf2 ++ powersOf10 ++ special ++
    (WorstCases.log2 ++ WorstCases.log10).map Float.ofBits

end Verified.Examples.Log2Accuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.Log2Accuracy in
def main : IO UInt32 := do
  unless (List.range 64).all tableEntryOk do
    IO.eprintln "fail: a table entry of log2 differs from its center"
    return 1
  for (name, f, base, library) in
      [("log2", Log2.log2, PowerReference.log2, Float.log2),
       ("log10", Log10.log10, PowerReference.log10, Float.log10)] do
    let mut ours : Tally := {}
    let mut lib : Tally := {}
    for x in args do
      let ref := reference base x
      let y := f x
      unless (distance y ref).any (· ≤ 1) do
        IO.eprintln s!"fail: {name} at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
        return 1
      ours := ours.add y ref
      lib := lib.add (library x) ref
    IO.println s!"log2 accuracy: {args.size} results of {name} lie within {units ours.worst} of \
      the reference, {ours.unequal} of them unequal"
    IO.println s!"log2 accuracy: the C library's {name} lies within {units lib.worst} of the \
      reference, {lib.unequal} unequal{lib.unorderedNote}"
  IO.println "log2 accuracy: the tables of log2 agree with their centers"
  return 0
