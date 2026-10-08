import Verified.Examples.Exp
import Verified.Examples.Reference

/-! A native check of `Exp.exp` against `Reference.exp` rounded to the nearest double.  Arm states
an error of 0.511 units in the last place, so each result must lie within one unit of the
reference.  The check first compares each table entry `H j · (1 + T j)` with `2 ^ (j/128)` from the
same series, within `2 ^ -100` relatively.  The arguments are evenly spaced values over the whole
range in which `exp` is finite and positive, hashed values over the exponents from `2 ^ -60` to
`2 ^ 10` with both signs, the doubles next to the thresholds of the code and of overflow and
underflow, and the special values.  It also reports, for information, the distance from the
reference of the C library's `exp`, which Lean's `Float.exp` calls.  The check exits with an error
at the first result further than one unit from the reference.  Run with
`lake env lean --run`. -/

namespace Verified.Examples.ExpAccuracy

open Verified.Examples Reference

/-- The double nearest to `exp x`. -/
def reference (x : Float) : Float :=
  if x.isNaN then x
  else if x.isInf then if x > 0.0 then x else 0.0
  else if x > 1100.0 then Float.ofBits 0x7FF0000000000000
  else if x < -1100.0 then 0.0
  else
    let q := precision x
    let (v, s) := Reference.exp (scaled x q) q
    toFloat v s

/-- Whether table entry `j` gives `2 ^ (j/128)` within `2 ^ -100` relatively. -/
def tableEntryOk (j : Nat) : Bool :=
  let t := Exp.expTable[2 * j]!
  let h := Exp.expTable[2 * j + 1]! + ((UInt64.ofNat j) <<< (45 : UInt64))
  let (hm, he) := exactValue (Float.ofBits h)
  let (tm, te) := exactValue (Float.ofBits t)
  -- `H (1 + T) · 2 ^ (2 P)`, with `H = hm 2 ^ he` and `T = tm 2 ^ te`, exact since `he + P` and
  -- `te + P` are positive.
  let product := Reference.shift (hm * (2 ^ P + Reference.shift tm (te + P))) (he + P)
  let exact := expFixed (j * ln2 P / 128) P * 2 ^ P
  (product - exact).natAbs * 2 ^ 100 ≤ exact.natAbs

def args : Array Float :=
  let edges := #[709.782712893384, 709.0, -708.3964185322641, -745.1332191019411, -745.0,
    -744.44007192138122, 512.0, -512.0, 1024.0, -1024.0, Float.ofBits 0x3C90000000000000,
    -Float.ofBits 0x3C90000000000000, 1.0, -1.0, 0.5].flatMap near
  let special := #[0.0, -0.0, Float.ofBits 0x7FF0000000000000, Float.ofBits 0xFFF0000000000000,
    Float.ofBits 0x7FF8000000000000, 1e300, -1e300, Float.ofBits 1, -Float.ofBits 1]
  evenly 120000 (-745.5) 710.0 ++ hashed 60000 13 963 71 ++ edges ++ special

end Verified.Examples.ExpAccuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.ExpAccuracy in
def main : IO UInt32 := do
  unless (List.range 128).all tableEntryOk do
    IO.eprintln "fail: a table entry differs from 2 ^ (j/128)"
    return 1
  let mut ours : Tally := {}
  let mut library : Tally := {}
  for x in args do
    let ref := reference x
    let y := Exp.exp x
    unless (distance y ref).any (· ≤ 1) do
      IO.eprintln s!"fail: exp at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
      return 1
    ours := ours.add y ref
    library := library.add (Float.exp x) ref
  IO.println s!"exp accuracy: the table agrees with 2 ^ (j/128), and {args.size} results lie \
    within {units ours.worst} of the reference, {ours.unequal} of them unequal"
  IO.println s!"exp accuracy: the C library's results lie within {units library.worst} of the \
    reference, {library.unequal} of them unequal{library.unorderedNote}"
  return 0
