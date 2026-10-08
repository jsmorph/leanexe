import Verified.Examples.Trig

/-! A native check of `Trig.sin` and `Trig.cos` against a reference computed with Lean's integers:
the reduction by a 2,400-bit `π` from Machin's formula, the Taylor series of `sin` and `cos` in
300-bit fixed point, and rounding to the nearest double.  fdlibm states an error below one unit in
the last place, so each result must lie within one unit of the reference.  The arguments are hashed
values over the exponents from `2 ^ -30` to `2 ^ 1023` with both signs, evenly spaced values up to
100, the doubles at and next to the rounded `k · π/2` for `k` up to 20,000, where the reduction
cancels, and five more with their negatives: `6381956970095103 · 2 ^ 797`, the double closest to a
multiple of `π/2`, `1647100`, just above `2 ^ 20 · π/2`, where the Payne–Hanek reduction begins,
`10 ^ 22`, `10 ^ 300`, and the largest finite double.  The check first compares the words of
`Trig.invPiWord` and `Trig.halfPiWord` with `2/π` and `π/2` from the same `π`.  It also reports,
for information, the distance from the reference of the C library's `sin` and `cos`, which Lean's
`Float.sin` and `Float.cos` call.  The check exits with an error at the first result further than
one unit from the reference, or at a NaN or infinity.  Run with `lake env lean --run`. -/

namespace Verified.Examples.TrigAccuracy

/-- The position of a finite float among the floats in order. -/
def order (x : Float) : Int :=
  let b := x.toBits
  if b >>> 63 == 1 then -((b &&& 0x7FFFFFFFFFFFFFFF).toNat : Int) else (b.toNat : Int)

/-- `arctan (1 / x) · 2 ^ p`, within a few units, by its alternating series. -/
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

/-- `π · 2 ^ 2400` by Machin's formula `π = 16 arctan (1/5) - 4 arctan (1/239)`, within a few
units. -/
def piScaled : Int := 4 * (4 * arctanInv 5 2400 - arctanInv 239 2400)

/-- The bits of the double nearest to `v · 2 ^ -300`, for `v` with a normal result. -/
def nearest (v : Int) : UInt64 :=
  if v == 0 then 0 else
    let a := v.natAbs
    let l := Nat.log2 a + 1
    let sh := l - 53
    let q := a >>> sh
    let r := a - (q <<< sh)
    let half := if sh == 0 then 0 else 2 ^ (sh - 1)
    let q := if sh != 0 && (r > half || (r == half && q % 2 == 1)) then q + 1 else q
    let (q, l) := if q == 2 ^ 53 then (q / 2, l + 1) else (q, l)
    let bits := (UInt64.ofNat (l + 1023 - 1 - 300) <<< 52) ||| UInt64.ofNat (q - 2 ^ 52)
    if v < 0 then bits ||| 0x8000000000000000 else bits

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
def reference (x : Float) : UInt64 × UInt64 :=
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
  if b >>> 63 == 1 then (nearest (-vs), nearest vc) else (nearest vs, nearest vc)

/-- The number of floats from `a` to `b`, when both are finite. -/
def distance (a b : Float) : Option Nat :=
  if a.isFinite && b.isFinite then some (order a - order b).natAbs else none

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

open Verified.Examples Verified.Examples.TrigAccuracy in
def main : IO UInt32 := do
  unless invPiWords == (List.range 20).map (Trig.invPiWord ∘ UInt64.ofNat) &&
      halfPiWords == [Trig.halfPiWord 0, Trig.halfPiWord 1] do
    IO.eprintln "fail: the words of 2/π or π/2 differ from those of Machin's formula"
    return 1
  let mut worst := 0
  let mut unequal := 0
  let mut libraryWorst := 0
  let mut libraryUnequal := 0
  for x in args do
    let (rs, rc) := reference x
    for (name, ours, library, ref) in
        [("sin", Trig.sin x, Float.sin x, rs), ("cos", Trig.cos x, Float.cos x, rc)] do
      let some d := distance ours (Float.ofBits ref)
        | IO.eprintln s!"fail: {name} at bits {x.toBits}: {ours.toBits}, the reference {ref}"
          return 1
      if 1 < d then
        IO.eprintln s!"fail: {name} at bits {x.toBits}: {ours.toBits}, the reference {ref}, {d} \
          units apart"
        return 1
      if 0 < d then unequal := unequal + 1
      worst := max worst d
      let some dl := distance library (Float.ofBits ref)
        | IO.eprintln s!"fail: the C library's {name} at bits {x.toBits}: {library.toBits}"
          return 1
      if 0 < dl then libraryUnequal := libraryUnequal + 1
      libraryWorst := max libraryWorst dl
  IO.println s!"trig accuracy: the words of 2/π and π/2 agree with Machin's formula, and \
    {2 * args.size} results lie within {worst} unit of the reference, {unequal} of them unequal"
  IO.println s!"trig accuracy: the C library's results lie within {libraryWorst} units of the \
    reference, {libraryUnequal} of them unequal"
  return 0
