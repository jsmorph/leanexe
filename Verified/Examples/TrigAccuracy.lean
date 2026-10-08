import Verified.Examples.Trig
import Verified.Examples.Reference

/-! A native check of `Trig.sin` and `Trig.cos` against a reference computed with Lean's integers:
the reduction by a 2,400-bit `π` from Machin's formula, the Taylor series of `sin` and `cos` in
300-bit fixed point, and `Reference.toFloat`'s rounding to the nearest double.  fdlibm states an
error below one unit in the last place, so each result must lie within one unit of the reference.
The arguments are hashed values over the exponents from `2 ^ -30` to `2 ^ 1023` with both signs,
evenly spaced values up to 100, the doubles at and next to the rounded `k · π/2` for `k` up to
20,000, where the reduction cancels, and five more with their negatives:
`6381956970095103 · 2 ^ 797`, the double closest to a multiple of `π/2`, `1647100`, just above
`2 ^ 20 · π/2`, where the Payne–Hanek reduction begins, `10 ^ 22`, `10 ^ 300`, and the largest
finite double.  The check first compares the words of the tables `Trig.invPi` and `Trig.halfPi`
with `2/π` and `π/2` from the same `π`.  It also reports, for information, the distance from the
reference of the C library's `sin` and `cos`, which Lean's `Float.sin` and `Float.cos` call.  The
check exits with an error at the first result further than one unit from the reference, or at a
NaN.  Run with `lake env lean --run`. -/

namespace Verified.Examples.TrigAccuracy

open Verified.Examples Reference

/-- `arctan (1 / x) · 2 ^ p` for `x ≥ 2`, by its alternating series, within `n + 2` units of the
exact value for `n` terms: each term is the floor of the exact term, and the terms omitted sum to
less than `4/3` units. -/
def arctanInv (x p : Nat) : Int := Id.run do
  let mut total : Int := 0
  let mut term : Nat := 2 ^ p / x
  let mut n := 1
  let mut sign : Int := 1
  while term != 0 do
    total := total + sign * (term / n : Nat)
    term := term / (x * x)
    n := n + 2
    sign := -sign
  return total

/-- `π · 2 ^ 2400` by Machin's formula `π = 16 arctan (1/5) - 4 arctan (1/239)`, within `2 ^ 14`
units, since the series have 517 and 152 terms. -/
def piScaled : Int := 4 * (4 * arctanInv 5 2400 - arctanInv 239 2400)

/-- The words of `2/π · 2 ^ 1216` from `piScaled`, the integer part first. -/
def invPiWords : List UInt64 :=
  let q := (2 ^ 3617 / piScaled).toNat
  (List.range 20).map fun k => UInt64.ofNat (q >>> (64 * (19 - k)))

/-- The words of `π/2 · 2 ^ 127` from `piScaled`, truncated, the high word first. -/
def halfPiWords : List UInt64 :=
  let q := (piScaled / 2 ^ 2274).toNat
  [UInt64.ofNat (q >>> 64), UInt64.ofNat q]

/-- `(sin x, cos x)` for a finite `x` with a normal result, by exact reduction and Taylor series in
300-bit fixed point, rounded to the nearest doubles. -/
def reference (x : Float) : Float × Float :=
  let b := x.toBits
  let frac := (b &&& 0xFFFFFFFFFFFFF).toNat
  let e := ((b >>> 52) &&& 0x7FF).toNat
  let (m, e) := if e == 0 then (frac, 1) else (frac + 2 ^ 52, e)
  -- `x · 2/π · 2 ^ 300 = m · 2 ^ (e - 1075 + 1 + 2400 + 300) / (π · 2 ^ 2400)`.
  let t : Int := (m * 2 ^ (e + 1626) : Nat) / piScaled
  let n := (t / 2 ^ 300) % 4
  let f := t % 2 ^ 300
  let (n, f) := if f ≥ 2 ^ 299 then ((n + 1) % 4, f - 2 ^ 300) else (n, f)
  -- `r · 2 ^ 300 = f · π/2`, with `|r| ≤ π/4`, so that the terms past the 70th are below
  -- `2 ^ -300`.
  let r := f * piScaled / 2 ^ 2401
  let one : Int := 2 ^ 300
  let (s, c) := Id.run do
    let mut s : Int := 0
    let mut c : Int := 0
    let mut term : Int := one
    for k in [1:71] do
      -- `term = r ^ (k - 1) / (k - 1)!`
      match (k - 1) % 4 with
      | 0 => c := c + term
      | 1 => s := s + term
      | 2 => c := c - term
      | _ => s := s - term
      term := term * r / one / k
    return (s, c)
  let (vs, vc) := match n.toNat with
    | 0 => (s, c)
    | 1 => (c, -s)
    | 2 => (-s, -c)
    | _ => (-c, s)
  (toFloat (if b >>> 63 == 1 then -vs else vs) (-300), toFloat vc (-300))

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
