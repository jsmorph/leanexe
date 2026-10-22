import Library.Numerics.Float64.Asinh.Program
import TestSupport.Numerics.WorstCases
import TestSupport.Numerics.HyperbolicReference

/-! A native check of `Library.Numerics.Float64.Asinh.asinh`, `Library.Numerics.Float64.Asinh.acosh`, and `Library.Numerics.Float64.Asinh.atanh` against references computed
with Lean's integers through `HyperbolicReference`, rounded to the nearest double.  fdlibm states no
error bound for any of them, and the check requires the largest distance it finds, two units in the
last place, for each of them.  The arguments of `asinh` are evenly spaced values from -10 to 10 and
hashed values over all exponents with both signs, those of `acosh` evenly spaced values from 1 to
10, hashed values from 1 up, and `1 + 2 ^ -k`, and those of `atanh` evenly spaced values from -1 to
1, hashed values over the exponents below 1 with both signs, and `±(1 - 2 ^ -k)`.  Each set adds the
doubles next to the high words that its code compares with and the special values.  The arguments
also include those of `WorstCases`, which give the largest known errors of thirteen libraries in
Tables 4 to 11 of the August 2026 report by Gladman, Innocente, Mather, Ozaki, and Zimmermann.  The
check also reports, for information, the distance from the reference of the C library's functions,
which Lean's `Float.asinh`, `Float.acosh`, and `Float.atanh` call.  It exits with an error at the
first result further from the reference than its bound.  Run with `lake env lean --run`. -/

namespace TestSupport.Numerics.AsinhAccuracy

open TestSupport.Numerics Reference HyperbolicReference

/-- The double nearest to `v · 2 ^ -q` with the sign `neg`. -/
def signed (neg : Bool) (v : Int) (q : Nat) : Float :=
  toFloat (if neg then -v else v) (-(q : Int))

/-- The double nearest to `asinh x`: at the precision of `x` plus 8 bits below `0.4` in magnitude
and at `P` above, where `|x|` scales to an exact integer, below a relative `2 ^ -380`. -/
def asinhReference (x : Float) : Float :=
  if x.isNaN || x.isInf || x == 0.0 then x
  else
    let q := if x.abs < 0.4 then precision x + 8 else P
    signed (x < 0.0) (asinhFixed (scaled x.abs q).toNat q) q

/-- The double nearest to `acosh x`, at precision `P`, where `x` scales to an exact integer, below
a relative `2 ^ -360`, since `acosh x ≥ 2 ^ -26` for every double above 1. -/
def acoshReference (x : Float) : Float :=
  if x.isNaN || x < 1.0 then Float.ofBits 0x7FF8000000000000
  else if x.isInf then x
  else if x == 1.0 then 0.0
  else signed false (acoshFixed (scaled x P).toNat P) P

/-- The double nearest to `atanh x`: up to `1/5` in magnitude `Reference.atanhFixed` at the
precision of `x` plus 8 bits, and above `atanhLog` at `P`, both below a relative `2 ^ -380`. -/
def atanhReference (x : Float) : Float :=
  if x.isNaN || x.abs > 1.0 then Float.ofBits 0x7FF8000000000000
  else if x.abs == 1.0 then
    Float.ofBits (if x < 0.0 then 0xFFF0000000000000 else 0x7FF0000000000000)
  else if x == 0.0 then x
  else if x.abs ≤ 0.2 then
    let q := precision x + 8
    signed (x < 0.0) (atanhFixed (scaled x.abs q).toNat q) q
  else
    let (m, e) := exactValue x.abs
    signed (x < 0.0) (atanhLog m.toNat e P) P

/-- `x` and `-x` for each `x`. -/
def both (xs : Array Float) : Array Float := xs.flatMap fun x => #[x, -x]

def special : Array Float :=
  #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 1.0, -1.0, 2.0, -2.0, 1e300, -1e300, 1e-300, -1e-300,
    Float.ofBits 1, Float.ofBits 0x8000000000000001, Float.ofBits 0x7FEFFFFFFFFFFFFF]

def edges (words : Array UInt64) : Array Float :=
  both (words.map Float.ofBits) |>.flatMap near

def asinhArgs : Array Float :=
  evenly 100000 (-10.0) 10.0 ++ hashed 100000 83 0 2047 ++
    edges #[0x3E30000000000000, 0x41B0000000000000, 0x4000000000000000] ++ special ++
    WorstCases.asinh.map Float.ofBits

def acoshArgs : Array Float :=
  let toOne := (Array.range 52).map fun k => 1.0 + Float.ofBits ((1022 - UInt64.ofNat k) <<< 52)
  evenly 100000 1.0 10.0 ++ (hashed 100000 89 1023 1024).map Float.abs ++ toOne ++
    edges #[0x3FF0000000000000, 0x41B0000000000000, 0x4000000000000000] ++ special ++
    WorstCases.acosh.map Float.ofBits

def atanhArgs : Array Float :=
  let toOne := both ((Array.range 53).map fun k =>
    1.0 - Float.ofBits ((1022 - UInt64.ofNat k) <<< 52))
  evenly 100000 (-1.0) 1.0 ++ hashed 100000 97 0 1023 ++ toOne ++
    edges #[0x3E30000000000000, 0x3FE0000000000000, 0x3FF0000000000000] ++ special ++
    WorstCases.atanh.map Float.ofBits

end TestSupport.Numerics.AsinhAccuracy

open TestSupport.Numerics TestSupport.Numerics.Reference TestSupport.Numerics.AsinhAccuracy in
def main : IO UInt32 := do
  let checks : List (String × Nat × Array Float × (Float → Float) × (Float → Float) ×
      (Float → Float)) :=
    [("asinh", 2, asinhArgs, Library.Numerics.Float64.Asinh.asinh, asinhReference, Float.asinh),
     ("acosh", 2, acoshArgs, Library.Numerics.Float64.Asinh.acosh, acoshReference, Float.acosh),
     ("atanh", 2, atanhArgs, Library.Numerics.Float64.Asinh.atanh, atanhReference, Float.atanh)]
  for (name, bound, args, f, reference, library) in checks do
    let mut ours : Tally := {}
    let mut lib : Tally := {}
    for x in args do
      let ref := reference x
      let y := f x
      unless (distance y ref).any (· ≤ bound) do
        IO.eprintln s!"fail: {name} at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
        return 1
      ours := ours.add y ref
      lib := lib.add (library x) ref
    IO.println s!"asinh accuracy: {args.size} results of {name} lie within {units ours.worst} of \
      the reference, {ours.unequal} of them unequal"
    IO.println s!"asinh accuracy: the C library's {name} lies within {units lib.worst} of the \
      reference, {lib.unequal} unequal{lib.unorderedNote}"
  return 0
