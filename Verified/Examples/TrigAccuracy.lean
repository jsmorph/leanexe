import Verified.Examples.Trig
import Verified.Examples.Reference

/-! A native check of `Trig.sin` and `Trig.cos` against `Reference.sinCos`, which reduces the
argument with a 2,400-bit `π` from Machin's formula and sums the Taylor series of `sin` and `cos`
in 300-bit fixed point, rounded to the nearest double.  fdlibm states an error below one unit in
the last place, so each result must lie within one unit of the reference.  The arguments are
hashed values over the exponents from `2 ^ -30` to `2 ^ 1023` with both signs, evenly spaced
values up to 100, the doubles at and next to the rounded `k · π/2` for `k` up to 20,000, where the
reduction cancels, and five more with their negatives: `6381956970095103 · 2 ^ 797`, the double
closest to a multiple of `π/2`, `1647100`, just above `2 ^ 20 · π/2`, where the Payne–Hanek
reduction begins, `10 ^ 22`, `10 ^ 300`, and the largest finite double.  The check first compares
the words of the tables `Trig.invPi` and `Trig.halfPi` with `2/π` and `π/2` from the same `π`.  It
also reports, for information, the distance from the reference of the C library's `sin` and
`cos`, which Lean's `Float.sin` and `Float.cos` call.  The check exits with an error at the first
result further than one unit from the reference, or at a NaN.  Run with
`lake env lean --run`. -/

namespace Verified.Examples.TrigAccuracy

open Verified.Examples Reference

/-- The words of `2/π · 2 ^ 1216` from `piWide`, the integer part first. -/
def invPiWords : List UInt64 :=
  let q := (2 ^ 3617 / piWide).toNat
  (List.range 20).map fun k => UInt64.ofNat (q >>> (64 * (19 - k)))

/-- The words of `π/2 · 2 ^ 127` from `piWide`, truncated, the high word first. -/
def halfPiWords : List UInt64 :=
  let q := (piWide / 2 ^ 2274).toNat
  [UInt64.ofNat (q >>> 64), UInt64.ofNat q]

/-- `(sin x, cos x)` from `Reference.sinCos` at 300 bits, whose error is below `2 ^ -292`, rounded
to the nearest doubles.  For the arguments of the check other than 0, where both values are exact,
each value is at least `2 ^ -61` in magnitude, so that its error is below a relative `2 ^ -231`. -/
def reference (x : Float) : Float × Float :=
  let (s, c) := sinCos x 300
  (toFloat s (-300), toFloat c (-300))

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
  hashed ++ even ++ multiples ++ hard ++ hard.map (- ·)

end Verified.Examples.TrigAccuracy

open Verified.Examples Verified.Examples.Reference Verified.Examples.TrigAccuracy in
def main : IO UInt32 := do
  unless invPiWords == Trig.invPi.toList && halfPiWords == Trig.halfPi.toList do
    IO.eprintln "fail: the words of 2/π or π/2 differ from those of Machin's formula"
    return 1
  let mut ours : Tally := {}
  let mut library : Tally := {}
  for x in args do
    let (rs, rc) := reference x
    for (name, y, l, ref) in
        [("sin", Trig.sin x, Float.sin x, rs), ("cos", Trig.cos x, Float.cos x, rc)] do
      unless (distance y ref).any (· ≤ 1) do
        IO.eprintln s!"fail: {name} at bits {x.toBits}: {y.toBits}, the reference {ref.toBits}"
        return 1
      ours := ours.add y ref
      library := library.add l ref
  IO.println s!"trig accuracy: the words of 2/π and π/2 agree with Machin's formula, and \
    {2 * args.size} results lie within {units ours.worst} of the reference, {ours.unequal} of \
    them unequal"
  IO.println s!"trig accuracy: the C library's results lie within {units library.worst} of the \
    reference, {library.unequal} of them unequal{library.unorderedNote}"
  return 0
