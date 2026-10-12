import Verified.Examples.Reference
import Verified.Examples.ArcReference

/-! Integer references for the Bessel functions of the first and second kinds, for the checks of
`Bessel`, in fixed point: `v` stands for `v · 2 ^ -q`.  Below 300 the power series give `J 0`,
`J 1`, `Y 0`, and `Y 1`, with Euler's constant from the algorithm of Brent and McMillan, and the
series of `J n` gives that function for any order below `max 300 n`.  From 300 up, Hankel's
asymptotic expansions give the functions of orders 0 and 1.  `Y n` comes from the forward recurrence
`Y (k + 1) = (2 k/x) Y k - Y (k - 1)`, and `J n` from `max 300 n` up from the same recurrence, where
it is stable.  The checks compare results in units of the modulus `√(J n ² + Y n ²)`, which is at
least `√(2/(π x))/2` for these orders, so each reference works at `Q` bits plus half the exponent of
`x` above 300, and leaves an error far below `2 ^ -52` times the modulus. -/

namespace Verified.Examples.BesselReference

open Verified.Examples Reference ArcReference

/-- Euler's constant `γ · 2 ^ q` by Brent and McMillan's algorithm B1, `A/B - ln n` with
`n = q/5 + 10`, whose error is below `π e ^ (-4 n) < 2 ^ (-q - 50)`.  The sums at `q + 40` bits
leave less than a unit after the division. -/
def eulerGamma (q : Nat) : Int := Id.run do
  let n := q / 5 + 10
  let g := q + 40
  let mut a : Int := -log n 0 g
  let mut b : Int := 2 ^ g
  let mut u := a
  let mut v := b
  let mut k := 1
  while a != 0 || b != 0 do
    b := b * (n * n) / (k * k)
    a := (a * (n * n) / k + b) / k
    u := u + a
    v := v + b
    k := k + 1
  return u * 2 ^ q / v

/-- `⌈m · 2 ^ e⌉` for `m > 0`. -/
def ceilValue (m : Nat) (e : Int) : Nat :=
  if e ≥ 0 then m * 2 ^ e.toNat else (m + 2 ^ (-e).toNat - 1) / 2 ^ (-e).toNat

/-- `(J 0, J 1, Y 0, Y 1) · 2 ^ q` for `x = m · 2 ^ e` below 300, from the power series
`J 0 = Σ (-1) ^ k (x²/4) ^ k/k!²`, `J 1 = (x/2) Σ (-1) ^ k (x²/4) ^ k/(k! (k + 1)!)`,
`Y 0 = (2/π) ((ln (x/2) + γ) J 0 - Σ (-1) ^ k H k (x²/4) ^ k/k!²)` with the harmonic numbers `H k`,
and the like series of `Y 1`, at `g = q + 80` bits plus `1.5 x` bits for the cancellation of the
alternating terms, whose largest is below `e ^ x`, plus the number of leading zero bits of a small
`x`, which keep `x · 2 ^ g` and the term `-2/(π x)` of `Y 1` exact to `q + 80` bits.  Each term and
sum truncates by less than a unit, and the logarithm, `π`, and `γ` add less than `2 ^ 14` units at
`g` bits, which the shift by 80 bits removes. -/
def series01 (m : Nat) (e : Int) (q : Nat) : Int × Int × Int × Int := Id.run do
  let g := q + 80 + ceilValue m e * 3 / 2 + 1 + (-(e + (Nat.log2 m : Int))).toNat
  let one : Int := 2 ^ g
  let z2 := shift (m * m) (2 * e + g - 2)
  let xh := shift m (e + g - 1)
  let mut t0 := one
  let mut t1 := one
  let mut h : Int := 0
  let mut k : Nat := 0
  let mut j0 : Int := 0
  let mut s0 : Int := 0
  let mut j1r : Int := 0
  let mut s1 : Int := 0
  while t0 != 0 || t1 != 0 do
    let hn := h + one / (k + 1)
    let sgn : Int := if k % 2 == 1 then -1 else 1
    j0 := j0 + sgn * t0
    s0 := s0 + sgn * (t0 * h / one)
    j1r := j1r + sgn * t1
    s1 := s1 + sgn * (t1 * (h + hn) / one)
    k := k + 1
    t0 := t0 * z2 / one / (k * k)
    t1 := t1 * z2 / one / (k * (k + 1))
    h := hn
  let j1 := j1r * xh / one
  let lnh := log m (e - 1) g
  let ga := eulerGamma g
  let pig := pi g
  let y0 := 2 * ((lnh + ga) * j0 / one - s0) * one / pig
  let xg := shift m (e + g)
  let t1v := -(2 * one * one) / xg
  let t2v := 2 * (lnh * j1 / one)
  let t3v := xh * (s1 - 2 * ga * j1r / one) / one
  let y1 := (t1v + t2v - t3v) * one / pig
  let d : Int := 2 ^ (g - q)
  return (j0 / d, j1 / d, y0 / d, y1 / d)

/-- Hankel's `P (ν, x)` and `Q (ν, x)` for `ν = 0, 1` at `g` bits, with `xg = x · 2 ^ g`: the terms
`a k (ν)/x ^ k` with `a k = (μ - 1)(μ - 9)⋯(μ - (2 k - 1)²)/(k! 8 ^ k)`, `μ = 4 ν²`, alternate
between `P` and `Q` with signs `(-1) ^ ⌊k/2⌋`, and the sums stop at the first term that vanishes at
`g` bits or stops decreasing.  For `x ≥ 300` the terms decrease to below `e ^ (-2 x) < 2 ^ -865`
before they grow, so the remainder is below a unit. -/
def hankelPQ (nu : Nat) (xg : Int) (g : Nat) : Int × Int := Id.run do
  let mu : Int := 4 * nu * nu
  let mut p : Int := 0
  let mut q : Int := 0
  let mut term : Int := 2 ^ g
  let mut k : Nat := 0
  let mut go := true
  while go do
    let sgn : Int := if (k / 2) % 2 == 0 then 1 else -1
    if k % 2 == 0 then p := p + sgn * term else q := q + sgn * term
    k := k + 1
    let nxt := term * (mu - ((2 * k - 1) * (2 * k - 1) : Nat)) / (8 * k) * 2 ^ g / xg
    if nxt == 0 || (nxt.natAbs ≥ term.natAbs && k > 2) then go := false
    else term := nxt
  return (p, q)

/-- `(J 0, J 1, Y 0, Y 1) · 2 ^ q` for a double `x ≥ 300` from Hankel's expansions at `g = q + 64`
bits: `J ν = √(2/(π x)) (P cos θ - Q sin θ)` and `Y ν = √(2/(π x)) (P sin θ + Q cos θ)` with
`θ = x - π/4 - ν π/2`, where `cos θ` and `sin θ` come from `Reference.sinCos` and `√2`.  The
reduction of `x` by `piWide` stays exact to a unit since `1023 + g < 2387`. -/
def hankel01 (x : Float) (q : Nat) : Int × Int × Int × Int :=
  let (m, e) := exactValue x
  let g := q + 64
  let one : Int := 2 ^ g
  let xg := shift m (e + g)
  let (s, c) := sinCos x g
  let (p0, q0) := hankelPQ 0 xg g
  let (p1, q1) := hankelPQ 1 xg g
  let amp : Int := isqrt (2 * 2 ^ (3 * g) / (pi g * xg / one).toNat)
  let r2 : Int := isqrt (2 * 2 ^ (2 * g))
  let inv := fun (v : Int) => v * one / r2
  let cm := inv (c + s)
  let sm := inv (s - c)
  let cm3 := inv (s - c)
  let sm3 := inv (-s - c)
  let j0 := amp * ((p0 * cm - q0 * sm) / one) / one
  let y0 := amp * ((p0 * sm + q0 * cm) / one) / one
  let j1 := amp * ((p1 * cm3 - q1 * sm3) / one) / one
  let y1 := amp * ((p1 * sm3 + q1 * cm3) / one) / one
  let d : Int := 2 ^ (g - q)
  (j0 / d, j1 / d, y0 / d, y1 / d)

/-- The base precision of the Bessel references. -/
def Q : Nat := 200

/-- The precision of the references at a finite `x > 0`: `Q` plus half the exponent of `x` from 300
up, so that the modulus, at least `√(2/(π x))/2`, keeps more than `Q - 2` bits. -/
def precisionAt (x : Float) : Nat :=
  let (m, e) := exactValue x
  if x < 300.0 then Q else Q + ((Nat.log2 m.natAbs : Int) + e).toNat / 2 + 2

/-- `(J 0, J 1, Y 0, Y 1) · 2 ^ q` at `q = precisionAt x` for a finite `x > 0`. -/
def bessel01 (x : Float) : Int × Int × Int × Int :=
  let (m, e) := exactValue x
  let q := precisionAt x
  if x < 300.0 then series01 m.toNat e q else hankel01 x q

/-- `J n · 2 ^ q` for `x = m · 2 ^ e > 0` and `n ≥ 0` from the series
`(x/2) ^ n Σ (-1) ^ k (x²/4) ^ k/(k! (n + k)!)` at `q + 80` bits plus `1.5 x` bits for the
cancellation and `4 n` bits for the truncation of `(x/2) ^ n/n!`. -/
def seriesN (n m : Nat) (e : Int) (q : Nat) : Int := Id.run do
  let g := q + 80 + ceilValue m e * 3 / 2 + 1 + 4 * n
  let one : Int := 2 ^ g
  let z2 := shift (m * m) (2 * e + g - 2)
  let xh := shift m (e + g - 1)
  let mut lead := one
  for j in [1:n + 1] do
    lead := lead * xh / one / j
  let mut t := lead
  let mut s : Int := 0
  let mut k : Nat := 0
  while t != 0 do
    s := s + (if k % 2 == 1 then -t else t)
    k := k + 1
    t := t * z2 / one / (k * (k + n))
  return s / 2 ^ (g - q)

/-- `(J n, Y n) · 2 ^ q` at `q = precisionAt x` for a finite `x > 0` and `n ≥ 0`.  `Y n` is the
forward recurrence from `Y 0` and `Y 1` at 200 more bits, which it may lose in its growth, plus the
number of leading zero bits of a small `x`, which keep `x · 2 ^ g` exact, and `J n` the same
recurrence from `J 0` and `J 1` from `max 300 n` up, and `seriesN` below. -/
def besselN (n : Nat) (x : Float) : Int × Int :=
  let (m, e) := exactValue x
  let q := precisionAt x
  let g := q + 200 + (-(e + (Nat.log2 m.natAbs : Int))).toNat
  let (j0, j1, y0, y1) :=
    if x < 300.0 then series01 m.toNat e g else hankel01 x g
  let xg := shift m (e + g)
  let one : Int := 2 ^ g
  let step := fun (s : Int × Int) (k : Nat) => (s.2, 2 * k * s.2 * one / xg - s.1)
  let yn :=
    if n == 0 then y0 else ((List.range (n - 1)).foldl (fun s k => step s (k + 1)) (y0, y1)).2
  let jn :=
    if n == 0 then j0
    else if x.toUInt64.toNat ≥ max 300 n then
      ((List.range (n - 1)).foldl (fun s k => step s (k + 1)) (j0, j1)).2
    else seriesN n m.toNat e g
  (jn / 2 ^ (g - q), yn / 2 ^ (g - q))

end Verified.Examples.BesselReference
