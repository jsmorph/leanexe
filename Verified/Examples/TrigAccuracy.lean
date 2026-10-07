import Verified.Examples.Trig

/-! A native check of `Trig.sin` and `Trig.cos` against the C library's `sin` and `cos`, which
Lean's `Float.sin` and `Float.cos` call, glibc's on Linux.  fdlibm and glibc each state an error
below one unit in the last place, so two such results lie at most one unit apart.  The check
covers hashed values over the exponents from `2 ^ -30` to the largest double, evenly spaced values
up to 100, the doubles next to `k · π/2` for `k` up to 20,000, where the reduction cancels, and the
largest doubles.  At `6381956970095103 · 2 ^ 797`, the double closest to a multiple of `π/2`,
glibc's `cos` is 8 units from the correctly rounded value, so that argument and a sample of huge
ones are checked against an exact reference instead: the reduction by a 2,400-bit `π` from
Machin's formula, the Taylor series of `sin` and `cos` in 300-bit fixed point, and rounding to the
nearest double, all in Lean's integers.  The check prints the largest distances and exits with an
error at the first result further than one unit from its reference, or at a NaN or infinity on one
side only.  Run with `lake env lean --run`. -/

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

/-- `(sin x, cos x)` correctly rounded, for a finite `x` with `2 ^ 20 ≤ |x|`, by exact reduction and
Taylor series in 300-bit fixed point. -/
def exactSinCos (x : Float) : UInt64 × UInt64 :=
  let b := x.toBits
  let m := ((b &&& 0xFFFFFFFFFFFFF) ||| 0x10000000000000).toNat
  let e := ((b >>> 52) &&& 0x7FF).toNat
  -- `x · 2/π · 2 ^ 300 = m · 2 ^ (e - 1075 + 1 + 2400 + 300) / (π · 2 ^ 2400)`.
  let t : Int := (m * 2 ^ (e + 1626) : Nat) / piScaled
  let n := (t / 2 ^ 300) % 4
  let f := t % 2 ^ 300
  let (n, f) := if f ≥ 2 ^ 299 then ((n + 1) % 4, f - 2 ^ 300) else (n, f)
  -- `r · 2 ^ 300 = f · π/2`.
  let r := f * piScaled / 2 ^ 2401
  let one : Int := 2 ^ 300
  let (s, c) := Id.run do
    let mut s : Int := 0
    let mut c : Int := 0
    let mut term : Int := one
    for k in [1:200] do
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

/-- The number of floats from `a` to `b`, when both are finite or both are the same non-finite
value. -/
def distance (a b : Float) : Option Nat :=
  if a.isNaN || b.isNaN then if a.isNaN && b.isNaN then some 0 else none
  else if a.isInf || b.isInf then if a == b then some 0 else none
  else some (order a - order b).natAbs

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
  hashed ++ even ++ multiples

/-- Arguments checked against the exact reference: the double closest to a multiple of `π/2`, the
largest doubles, and hashed huge values, with their negatives. -/
def exactArgs : Array Float :=
  let hard : Array Float :=
    #[Float.ofBits (((1872 : UInt64) <<< (52 : UInt64)) ||| (6381956970095103 - 4503599627370496)),
      1e22, 1e300, Float.ofBits 0x7FEFFFFFFFFFFFFF, 1647100.0]
  let huge := (Array.range 300).map fun i =>
    let h := (UInt64.ofNat i + 11) * 0xbf58476d1ce4e5b9
    let e : UInt64 := 1044 + (h >>> (52 : UInt64)) % 1003
    Float.ofBits ((e <<< (52 : UInt64)) ||| (h &&& 0xFFFFFFFFFFFFF))
  (hard ++ huge) ++ (hard ++ huge).map (- ·)

end Verified.Examples.TrigAccuracy

open Verified.Examples Verified.Examples.TrigAccuracy in
def main : IO UInt32 := do
  let mut worst := 0
  let mut count := 0
  let mut unequal := 0
  for x in args do
    for (name, ours, ref) in [("sin", Trig.sin x, Float.sin x), ("cos", Trig.cos x, Float.cos x)] do
      count := count + 1
      match distance ours ref with
      | none =>
        IO.eprintln s!"fail: {name} at bits {x.toBits}: {ours.toBits}, the C library {ref.toBits}"
        return 1
      | some d =>
        if 1 < d then
          IO.eprintln s!"fail: {name} at bits {x.toBits}: {ours.toBits}, the C library \
            {ref.toBits}, {d} units apart"
          return 1
        if 0 < d then unequal := unequal + 1
        worst := max worst d
  IO.println s!"trig accuracy: {count} results within {worst} unit of the C library's, \
    {unequal} of them unequal"
  let mut exactWorst := 0
  let mut exactUnequal := 0
  let mut libraryWorst := 0
  for x in exactArgs do
    let (rs, rc) := exactSinCos x
    for (name, ours, library, ref) in
        [("sin", Trig.sin x, Float.sin x, rs), ("cos", Trig.cos x, Float.cos x, rc)] do
      let some d := distance ours (Float.ofBits ref)
        | IO.eprintln s!"fail: {name} at bits {x.toBits}: {ours.toBits}, exactly {ref}"
          return 1
      if 1 < d then
        IO.eprintln s!"fail: {name} at bits {x.toBits}: {ours.toBits}, exactly {ref}, {d} units \
          apart"
        return 1
      if 0 < d then exactUnequal := exactUnequal + 1
      exactWorst := max exactWorst d
      libraryWorst := max libraryWorst ((distance library (Float.ofBits ref)).getD 0)
  IO.println s!"trig accuracy: {2 * exactArgs.size} results within {exactWorst} unit of the exact \
    ones, {exactUnequal} of them unequal; the C library's within {libraryWorst} units"
  return 0
