import Verified.Examples.Exp2
import Verified.Examples.PowerReference

/-! A native check of `Exp2.exp2` and `Exp2.exp10` against references computed with Lean's integers
through `PowerReference.exp2` and `PowerReference.exp10`, rounded to the nearest double.  Arm states
errors near 0.51 units in the last place, so each result must lie within one unit of the reference.
The arguments of `exp2` are evenly spaced values from -1100 to 1100, hashed values over the
exponents from `2 ^ -60` to `2 ^ 10` with both signs, the integers from -1080 to 1030 and the
halves between them, and the doubles next to the code's thresholds: `2 ^ -54`, 512, 928, 1024,
-1022, -1074, -1075, and -1076.  Those of `exp10` are evenly spaced values from -400 to 400, hashed
values over the same exponents, the integers from -330 to 310, and the doubles next to `2 ^ -57`,
256, `log10 (DBL_MAX)`, -350, and -307.65.  Both sets add the special values.  The check also
reports, for information, the distance from the reference of the C library's `exp2`, which Lean's
`Float.exp2` calls.  Lean has no binding of `exp10`.  The check exits with an error at the first
result further than one unit from the reference.  Run with `lake env lean --run`. -/

namespace Verified.Examples.Exp2Accuracy

open Verified.Examples Reference

/-- The double nearest to `2 ^ x`, within a relative `2 ^ -390` at precision `P`.  From 1100 on in
magnitude the result overflows or underflows to 0. -/
def exp2Reference (x : Float) : Float :=
  if x.isNaN then x
  else if x.isInf then if x < 0.0 then 0.0 else x
  else if x ≥ 1100.0 then Float.ofBits 0x7FF0000000000000
  else if x ≤ -1100.0 then 0.0
  else
    let (v, s) := PowerReference.exp2 (scaled x P) P
    toFloat v s

/-- The double nearest to `10 ^ x`, within a relative `2 ^ -386` at precision `P`.  From 400 on in
magnitude the result overflows or underflows to 0. -/
def exp10Reference (x : Float) : Float :=
  if x.isNaN then x
  else if x.isInf then if x < 0.0 then 0.0 else x
  else if x ≥ 400.0 then Float.ofBits 0x7FF0000000000000
  else if x ≤ -400.0 then 0.0
  else
    let (v, s) := PowerReference.exp10 (scaled x P) P
    toFloat v s

/-- `x` and `-x` for each `x`. -/
def both (xs : Array Float) : Array Float := xs.flatMap fun x => #[x, -x]

def special : Array Float :=
  #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 1.0, -1.0, 1e300, -1e300, 1e-300, -1e-300, Float.ofBits 1,
    Float.ofBits 0x8000000000000001, Float.ofBits 0x7FEFFFFFFFFFFFFF,
    Float.ofBits 0xFFEFFFFFFFFFFFFF]

def exp2Args : Array Float :=
  let integers := (Array.range 2111).flatMap fun i =>
    let k := (UInt64.ofNat i).toFloat - 1080.0
    #[k, k + 0.5]
  let edges := (#[Float.ofBits 0x3C90000000000000, 512.0, 928.0, 1024.0] |> both) ++
    #[-1022.0, -1074.0, -1075.0, -1076.0]
  evenly 100000 (-1100.0) 1100.0 ++ hashed 100000 101 963 70 ++ integers ++ edges.flatMap near ++
    special

def exp10Args : Array Float :=
  let integers := (Array.range 641).map fun i => (UInt64.ofNat i).toFloat - 330.0
  let edges := (#[Float.ofBits 0x3C60000000000000, 256.0, Float.ofBits 0x40734413509F79FF,
    350.0, 307.65] |> both)
  evenly 100000 (-400.0) 400.0 ++ hashed 100000 103 963 70 ++ integers ++ edges.flatMap near ++
    special

end Verified.Examples.Exp2Accuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.Exp2Accuracy in
def main : IO UInt32 := do
  let mut ours : Tally := {}
  let mut library : Tally := {}
  for x in exp2Args do
    let ref := exp2Reference x
    let y := Exp2.exp2 x
    unless (distance y ref).any (· ≤ 1) do
      IO.eprintln s!"fail: exp2 at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
      return 1
    ours := ours.add y ref
    library := library.add (Float.exp2 x) ref
  IO.println s!"exp2 accuracy: {exp2Args.size} results of exp2 lie within {units ours.worst} of \
    the reference, {ours.unequal} of them unequal"
  IO.println s!"exp2 accuracy: the C library's exp2 lies within {units library.worst} of the \
    reference, {library.unequal} unequal{library.unorderedNote}"
  let mut tens : Tally := {}
  for x in exp10Args do
    let ref := exp10Reference x
    let y := Exp2.exp10 x
    unless (distance y ref).any (· ≤ 1) do
      IO.eprintln s!"fail: exp10 at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
      return 1
    tens := tens.add y ref
  IO.println s!"exp2 accuracy: {exp10Args.size} results of exp10 lie within {units tens.worst} \
    of the reference, {tens.unequal} of them unequal"
  return 0
