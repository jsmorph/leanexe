/-! Exact references for the accuracy checks of the transcendental functions, computed with Lean's
integers.  A fixed-point value at precision `q` is an integer `v` that stands for `v · 2 ^ -q`.
`ln 2` comes from `ln 2 = 2 atanh (1/3)` and `π` from Machin's formula, `exp`, `sin`, and `cos`
from reductions by them and Taylor series, `log` from `atanh`, and the rounding to the nearest
double covers subnormals, zero, and overflow.  Each definition
states the error that its truncations leave, which is below a relative `2 ^ -230` for every value
that a check compares unit by unit.  A reference can round the wrong way only where the exact
value lies that near a midpoint between doubles, and then the two doubles beside the midpoint are
the only ones within one unit of it, so a check of one unit passes for the result either way. -/

namespace Verified.Examples.Reference

/-- The number of bits after the binary point at which the references compute for an argument of
magnitude at least 1. -/
def P : Nat := 400

/-- `atanh (1 / x) · 2 ^ w` for `x ≥ 2`, less than `n + 2` units below the exact value for `n`
terms: each term is the floor of the exact term, and the terms omitted sum to less than `4/3`
units. -/
def atanhInv (x w : Nat) : Int := Id.run do
  let mut total : Int := 0
  let mut power : Nat := 2 ^ w / x
  let mut n := 1
  while power != 0 do
    total := total + (power / n : Nat)
    power := power / (x * x)
    n := n + 2
  return total

/-- The precision of `ln2Wide`. -/
def W : Nat := 2400

/-- `ln 2 · 2 ^ W` as `2 atanh (1/3)`, less than `2 ^ 11` units below the exact value, since the
series has 757 terms. -/
def ln2Wide : Int := 2 * atanhInv 3 W

/-- `ln 2 · 2 ^ q` for `q ≤ W - 11`, less than two units below the exact value. -/
def ln2 (q : Nat) : Int := ln2Wide / 2 ^ (W - q)

/-- `exp (r · 2 ^ -q) · 2 ^ q` for `|r| ≤ 2 ^ (q - 1)`, by the Taylor series.  Each term is
truncated twice, so that its error stays below 4 units, and the series stops at the first term that
truncates to zero, so that the error is less than `4 n + 8` units for `n` terms. -/
def expFixed (r : Int) (q : Nat) : Int := Id.run do
  let one : Int := 2 ^ q
  let mut sum : Int := 0
  let mut term : Int := one
  let mut n : Int := 1
  while term != 0 do
    sum := sum + term
    term := term * r / one / n
    n := n + 1
  return sum

/-- `v · 2 ^ e`, truncated toward zero. -/
def shift (v e : Int) : Int :=
  if e ≥ 0 then v * 2 ^ e.toNat
  else
    let a := v.natAbs / 2 ^ (-e).toNat
    if v < 0 then -(a : Int) else a

/-- `exp (x · 2 ^ -q)` as `(v, s)` for `v · 2 ^ s`, for `q ≤ 2000` and `|x · 2 ^ -q| < 1100`, by
the reduction `x = k ln 2 + r` with `|r| ≤ ln 2/2` and `exp x = 2 ^ k exp r`.  The error of `ln 2`
moves `r` by less than `2 |k| < 2 ^ 12` units, and the series errs by less than `2 ^ 10` units,
with `exp r > 0.7`, so `v · 2 ^ s` lies within a relative `2 ^ (13 - q)` of the exact value. -/
def exp (x : Int) (q : Nat) : Int × Int :=
  let l := ln2 q
  let k := (2 * x + l) / (2 * l)
  (expFixed (x - k * l) q, k - q)

/-- `expm1 (y) · 2 ^ q` for `y = x · 2 ^ -q`, truncated, within a relative
`2 ^ (15 - q) / min 1 |y|` of the exact value: the error of `exp` is less than `2 ^ 13 exp y`
units, the truncation adds less than one, and `|expm1 y|` is at least
`0.63 · max 1 (exp y) · min 1 |y|`. -/
def expm1 (x : Int) (q : Nat) : Int :=
  let (v, s) := exp x q
  shift v (s + q) - 2 ^ q

/-- `tanh (y) · 2 ^ q` for `y = x · 2 ^ -q`, truncated, as `E / (E + 2)` with
`E = expm1 (2 |y|)`, within a relative `2 ^ (16 - q) / min 1 |y|` of the exact value: the
quotient's relative error is at most `E`'s, and the truncation adds at most one unit of
`tanh |y| ≥ min 1 |y| / 2`. -/
def tanh (x : Int) (q : Nat) : Int :=
  let e := expm1 (2 * x.natAbs) q
  let t := e * 2 ^ q / (e + 2 ^ (q + 1))
  if x < 0 then -t else t

/-- `atanh (s · 2 ^ -q) · 2 ^ q` for `s ≤ 2 ^ q / 5`, by its series, less than `2 n + 3` units
below the exact value for `n` terms: `s²` and each power lose less than a unit to truncation, so
that a power lies less than 2.1 units below its exact value, each quotient loses one more, and the
terms omitted sum to less than one unit. -/
def atanhFixed (s q : Nat) : Nat := Id.run do
  let s2 := s * s / 2 ^ q
  let mut total := 0
  let mut term := s
  let mut n := 1
  while term != 0 do
    total := total + term / n
    term := term * s2 / 2 ^ q
    n := n + 2
  return total

/-- `ln (m · 2 ^ e) · 2 ^ q` for `m > 0`, `q ≤ 500`, and `|j| ≤ 2 ^ 11`, which every double meets,
as `j ln 2 + 2 atanh ((y - 1)/(y + 1))` with `m · 2 ^ e = y · 2 ^ j` and `3/4 ≤ y < 3/2`, so that
`|(y - 1)/(y + 1)| ≤ 1/5`.  The
truncated quotient and the series leave less than `2 ^ 9` units, and `ln 2` less than
`2 |j| ≤ 2 ^ 12` more, so that the value lies within `2 ^ 13` units of the exact one, and within
`2 ^ 9` when `j = 0`. -/
def log (m : Nat) (e : Int) (q : Nat) : Int :=
  let L := Nat.log2 m
  let L := if 2 * m ≥ 3 * 2 ^ L then L + 1 else L
  let num : Int := (m : Int) - 2 ^ L
  let a : Int := 2 * atanhFixed (num.natAbs * 2 ^ q / (m + 2 ^ L)) q
  (e + L) * ln2 q + if num < 0 then -a else a

/-- `arctan (1 / x) · 2 ^ w` for `x ≥ 2`, by its alternating series, within `n + 1` units of the
exact value for `n` terms: each term is the floor of the exact term, and the terms omitted sum to
less than the first of them, which is below one unit. -/
def arctanInv (x w : Nat) : Int := Id.run do
  let mut total : Int := 0
  let mut term : Nat := 2 ^ w / x
  let mut n := 1
  let mut sign : Int := 1
  while term != 0 do
    total := total + sign * (term / n : Nat)
    term := term / (x * x)
    n := n + 2
    sign := -sign
  return total

/-- `π · 2 ^ W` by Machin's formula `π = 16 arctan (1/5) - 4 arctan (1/239)`, within `2 ^ 14`
units, since the series have 517 and 152 terms. -/
def piWide : Int := 4 * (4 * arctanInv 5 W - arctanInv 239 W)

/-- `π · 2 ^ q` for `q ≤ W - 14`, within two units. -/
def pi (q : Nat) : Int := piWide / 2 ^ (W - q)

/-- `(sin ρ, cos ρ) · 2 ^ q` for `ρ = r · 2 ^ -q` with `|ρ| ≤ 1`, by the Taylor series at `|ρ|`.
Each term is the floor of `|ρ| ^ k / k! · 2 ^ q` computed from the one before, less than two units
below the exact term, and the series stops at the first term that is zero, so that each value lies
within `2 n + 2` units of the exact one for `n` terms. -/
def sinCosFixed (r : Int) (q : Nat) : Int × Int := Id.run do
  let a := r.natAbs
  let mut s : Int := 0
  let mut c : Int := 0
  let mut term : Nat := 2 ^ q
  let mut k := 0
  while term != 0 do
    match k % 4 with
    | 0 => c := c + term
    | 1 => s := s + term
    | 2 => c := c - term
    | _ => s := s - term
    k := k + 1
    term := term * a / 2 ^ q / k
  return (if r < 0 then -s else s, c)

/-- `(sin, cos)` of `k π/2 + ρ` from `(sin ρ, cos ρ)`. -/
def quadrant (k : Nat) (s c : Int) : Int × Int :=
  match k % 4 with
  | 0 => (s, c)
  | 1 => (c, -s)
  | 2 => (-s, -c)
  | _ => (-c, s)

/-- `(sin θ, cos θ) · 2 ^ q` for `θ = 2 π num / den`, `den > 0`, and `q ≤ W - 14`, from the
nearest multiple `k π/2` of `θ` and the series at `θ - k π/2`.  The error of `π` moves the reduced
angle by less than half a unit and its truncation by less than one, so that each value lies within
`2 n + 4` units of the exact one for `n` terms of the series. -/
def sinCosTurns (num den q : Nat) : Int × Int :=
  let k := (8 * num + den) / (2 * den)
  let (s, c) := sinCosFixed ((((4 * num : Nat) : Int) - (k * den : Nat)) * pi q / (2 * den)) q
  quadrant k s c

/-- `v / 2 ^ n` rounded to the nearest integer, ties to even. -/
def roundShift (v n : Nat) : Nat :=
  if n == 0 then v
  else
    let q := v >>> n
    let rem := v - (q <<< n)
    let half := 2 ^ (n - 1)
    if rem > half || (rem == half && q % 2 == 1) then q + 1 else q

/-- The bits of the double nearest to `v · 2 ^ s`: a normal number, a subnormal, zero, or `∞`. -/
def roundBits (v : Nat) (s : Int) : UInt64 :=
  if v == 0 then 0
  else
    let e : Int := (Nat.log2 v : Int) + s
    if e ≥ 1024 then 0x7FF0000000000000
    else
      let quantum : Int := if e ≥ -1022 then e - 52 else -1074
      let sh := s - quantum
      let q := if sh ≥ 0 then v <<< sh.toNat else roundShift v (-sh).toNat
      if e ≥ -1022 then
        let (q, e) := if q == 2 ^ 53 then (2 ^ 52, e + 1) else (q, e)
        if e ≥ 1024 then 0x7FF0000000000000
        else UInt64.ofNat (((e + 1023).toNat <<< 52) + (q - 2 ^ 52))
      else UInt64.ofNat q

/-- The double nearest to `v · 2 ^ s`, with the sign of `v`. -/
def toFloat (v s : Int) : Float :=
  let bits := roundBits v.natAbs s
  Float.ofBits (if v < 0 then bits ||| 0x8000000000000000 else bits)

/-- The exact value of a finite double `y` as `(n, e)` for `n · 2 ^ e`. -/
def exactValue (y : Float) : Int × Int :=
  let b := y.toBits
  let frac := (b &&& 0xFFFFFFFFFFFFF).toNat
  let ex := ((b >>> 52) &&& 0x7FF).toNat
  let (m, ex) := if ex == 0 then (frac, 1) else (frac + 2 ^ 52, ex)
  ((if b >>> 63 == 1 then -(m : Int) else m), (ex : Int) - 1075)

/-- `x · 2 ^ q`, truncated toward zero, for a finite `x`. -/
def scaled (x : Float) (q : Nat) : Int :=
  let (m, e) := exactValue x
  shift m (e + q)

/-- The precision of the references for a finite nonzero `x`: `P` for `|x| ≥ 1`, and `P - e` for
`2 ^ e ≤ |x| < 1`, at most 1474.  `scaled x (precision x)` is exact and at least `2 ^ P` in
magnitude. -/
def precision (x : Float) : Nat :=
  let (m, e) := exactValue x
  P + (-((Nat.log2 m.natAbs : Int) + e)).toNat

/-- `(sin x, cos x) · 2 ^ q` for a finite `x` and `q ≤ 300`, from the nearest multiple `k π/2` of
`|x|` and the series at `|x| - k π/2`, which has at most 70 terms.  `|x| · 2/π · 2 ^ q` comes from
`piWide`, whose relative error is below `2 ^ -2387`, within two units, so that the reduced angle
lies within 5 units and each value within `2 ^ 8` units of the exact one. -/
def sinCos (x : Float) (q : Nat) : Int × Int :=
  let (m, e) := exactValue x
  let t : Int := (m.natAbs * 2 ^ (e + W + 1 + q).toNat : Nat) / piWide
  let k := (t / 2 ^ q).toNat + if t % 2 ^ q ≥ 2 ^ (q - 1) then 1 else 0
  let (s, c) := sinCosFixed ((t - k * 2 ^ q) * piWide / 2 ^ (W + 1)) q
  let (s, c) := quadrant k s c
  if m < 0 then (-s, c) else (s, c)

/-- The position of a float that is not NaN among the floats in order, in which `∞` follows the
largest finite double and `0` and `-0` share a position. -/
def order (x : Float) : Int :=
  let b := x.toBits
  if b >>> 63 == 1 then -((b &&& 0x7FFFFFFFFFFFFFFF).toNat : Int) else (b.toNat : Int)

/-- The number of floats from `a` to `b`, with 0 when both are NaN and `none` when one is. -/
def distance (a b : Float) : Option Nat :=
  if a.isNaN || b.isNaN then if a.isNaN && b.isNaN then some 0 else none
  else some (order a - order b).natAbs

/-- The largest distance of results from their references, the number of results unequal to them,
and the number of results that are NaN where the reference is not, or the reverse. -/
structure Tally where
  worst : Nat := 0
  unequal : Nat := 0
  unordered : Nat := 0

def Tally.add (t : Tally) (result reference : Float) : Tally :=
  match distance result reference with
  | some d => { t with worst := max t.worst d, unequal := t.unequal + if d == 0 then 0 else 1 }
  | none => { t with unordered := t.unordered + 1 }

/-- The clause that reports the results that are NaN where the reference is not, or the reverse,
empty when there are none. -/
def Tally.unorderedNote (t : Tally) : String :=
  if t.unordered == 0 then ""
  else s!", and {t.unordered} NaN where the reference is not, or the reverse"

/-- `1 unit` or `n units`. -/
def units (n : Nat) : String := if n == 1 then "1 unit" else s!"{n} units"

/-- The doubles at and next to `x`, two on each side. -/
def near (x : Float) : Array Float :=
  let b := x.toBits
  #[b - 2, b - 1, b, b + 1, b + 2].map Float.ofBits

/-- `count` hashed doubles with biased exponents from `lo` to `lo + span - 1` and both signs. -/
def hashed (count : Nat) (seed lo span : UInt64) : Array Float :=
  (Array.range count).map fun i =>
    let h := (UInt64.ofNat i + seed) * 0x9e3779b97f4a7c15
    let e : UInt64 := lo + (h >>> (52 : UInt64)) % span
    let x := Float.ofBits ((e <<< 52) ||| (h &&& 0xFFFFFFFFFFFFF))
    if h &&& 0x8000 == 0 then x else -x

/-- `count + 1` evenly spaced doubles from `a` to `b`. -/
def evenly (count : Nat) (a b : Float) : Array Float :=
  (Array.range (count + 1)).map fun i =>
    a + (UInt64.ofNat i).toFloat * ((b - a) / (UInt64.ofNat count).toFloat)

end Verified.Examples.Reference
