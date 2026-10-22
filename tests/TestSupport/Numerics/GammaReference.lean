import TestSupport.Numerics.Reference

/-! An integer reference for `lgamma` and `Γ`, for the checks of `Tgamma` and `Lgamma`.  For
`y > 0`, `lgamma y = lgamma (y + N) - ln (y (y + 1) ⋯ (y + N - 1))` with `y + N ≥ 300`, where
Stirling's series with 60 terms gives `lgamma (y + N)` with a remainder below `2 ^ -650`, and one
logarithm of the exact product gives the sum of the `N` logarithms.  For `x < 0`, the reflection
`lgamma x = ln π - ln |sin (π x)| - lgamma (1 - x)` applies, with the sign of `Γ x` that of
`sin (π x)`.  `Γ x` is the exponential of `lgamma x` with that sign.  A Python model of these
definitions, `lgamma` at 600 bits and `Γ` from it, gave the same doubles as CORE-MATH's correctly
rounded `tgamma` and `lgamma` at 3,500 arguments, 7,000 results: uniform random values in
`(-190, 175)` and `(-4, 4)` and random powers of two times `[1, 2)` from `2 ^ -1074` to `2 ^ 20`
with both signs. -/

namespace TestSupport.Numerics.GammaReference

open Reference

/-- `a/b` in lowest terms for `b > 0`. -/
def reduce (a : Int) (b : Nat) : Int × Nat :=
  let g := Nat.gcd a.natAbs b
  (a / g, b / g)

/-- The Bernoulli numbers `B 0` to `B n` as fractions, by the algorithm of Akiyama and Tanigawa,
which gives `B 1 = 1/2`; the series uses only the even ones. -/
def bernoulli (n : Nat) : Array (Int × Nat) := Id.run do
  let mut a : Array (Int × Nat) := Array.replicate (n + 1) (0, 1)
  let mut out : Array (Int × Nat) := #[]
  for m in [0:n + 1] do
    a := a.set! m (1, m + 1)
    for k in [0:m] do
      let j := m - k
      let (p, q) := a[j - 1]!
      let (r, s) := a[j]!
      a := a.set! (j - 1) (reduce (j * (p * s - r * q)) (q * s))
    out := out.push a[0]!
  return out

/-- The coefficients `B (2 k)/(2 k (2 k - 1))` of Stirling's series for `k` from 1 to 60. -/
def stirlingCoefficients : Array (Int × Nat) :=
  let b := bernoulli 120
  (Array.range 60).map fun i =>
    let k := i + 1
    let (p, q) := b[2 * k]!
    reduce p (q * (2 * k * (2 * k - 1)))

/-- `lgamma z · 2 ^ g` for `z = zm · 2 ^ ze ≥ 300`, from Stirling's series
`(z - 1/2) ln z - z + ln (2 π)/2 + Σ B (2 k)/(2 k (2 k - 1) z ^ (2 k - 1))`, whose remainder after
60 terms lies below `2 ^ -650`.  `Reference.log` leaves less than `2 ^ 13` units in each logarithm
at the precisions used here, up to 1,800 bits, since its series' error grows to below `2 ^ 11` units
there, and each truncation leaves less than 2 units, so that the result lies within `2 ^ 14 (z + 1)`
units, a relative `2 ^ (13 - g)` of `lgamma z ≥ z`. -/
def stirling (zm : Nat) (ze : Int) (g : Nat) : Int := Id.run do
  let one : Int := 2 ^ g
  let lz := log zm ze g
  let zg := shift zm (ze + g)
  let halfLn2pi := (log 2 0 g + log (pi g).toNat (-(g : Int)) g) / 2
  let mut st := (zg - one / 2) * lz / one - zg + halfLn2pi
  let invZ := one * one / zg
  let invZ2 := invZ * invZ / one
  let mut p := invZ
  for (num, den) in stirlingCoefficients do
    st := st + num * p / den
    p := p * invZ2 / one
  return st

/-- `lgamma y · 2 ^ q` for `y = m · 2 ^ e > 0`, computed at `g = q + 80` bits from `lgamma (y + N)`
and the logarithm of the exact product `y (y + 1) ⋯ (y + N - 1)`.  Below 300 the error is below
`2 ^ 25` units at `g` bits, less than a unit after the shift by 80 bits, and above 300 it is below a
relative `2 ^ (13 - g)`. -/
def lgammaPositive (m : Nat) (e : Int) (q : Nat) : Int :=
  let g := q + 80
  let (a, s) : Nat × Nat := if e ≥ 0 then (m * 2 ^ e.toNat, 0) else (m, (-e).toNat)
  let n := if a ≥ 300 * 2 ^ s then 0 else (300 * 2 ^ s - a + 2 ^ s - 1) / 2 ^ s
  let prod := (List.range n).foldl (fun acc j => acc * (a + j * 2 ^ s)) 1
  let lp := if n == 0 then 0 else log prod (-((n * s : Nat) : Int)) g
  (stirling (a + n * 2 ^ s) (-(s : Int)) g - lp) / 2 ^ (g - q)

/-- `(lgamma x · 2 ^ q, s)` for a finite `x` other than 0 and the negative integers, with `s` the
sign of `Γ x`.  For `x < 0` the reflection computes at `q + 40` bits plus the number of leading zero
bits of `|x|`, so that `sin (π x)` keeps its relative precision. -/
def lgammaFixed (x : Float) (q : Nat) : Int × Int :=
  let (m, e) := exactValue x
  if m > 0 then (lgammaPositive m.toNat e q, 1)
  else
    let am := m.natAbs
    let lead : Int := e + Nat.log2 am + 1
    let g := q + 40 + (if lead < 0 then (-lead).toNat else 0)
    let (s, _) := sinCosTurns am (2 ^ (1 - e).toNat) g
    let l := log (pi g).toNat (-(g : Int)) g - log s.natAbs (-(g : Int)) g -
      lgammaPositive (2 ^ (-e).toNat + am) e g
    (l / 2 ^ (g - q), if s > 0 then -1 else 1)

/-- The precision of the references. -/
def Q : Nat := 600

/-- Whether `x` is a finite negative integer. -/
def negativeInteger (x : Float) : Bool :=
  if x < 0.0 && !x.isInf then
    let (m, e) := exactValue x
    e ≥ 0 || m.natAbs % 2 ^ (-e).toNat == 0
  else false

/-- The double nearest to `Γ x`, with C's special values: `Γ (±0) = ±∞`, NaN at the negative
integers and `-∞`, and `+∞` at `+∞`.  An `lgamma` above 710 overflows, and one below -800 rounds to
a zero of the sign of `Γ x`. -/
def tgammaReference (x : Float) : Float :=
  if x.isNaN then x
  else if x.isInf then if x > 0.0 then x else Float.ofBits 0x7FF8000000000000
  else if x == 0.0 then 1.0 / x
  else if negativeInteger x then Float.ofBits 0x7FF8000000000000
  else
    let (l, s) := lgammaFixed x Q
    if l > 710 * 2 ^ Q then (if s > 0 then 1.0 else -1.0) / 0.0
    else if l < -800 * 2 ^ Q then if s > 0 then 0.0 else -0.0
    else
      let (v, e) := Reference.exp l Q
      toFloat (s * v) e

/-- The double nearest to `lgamma x`, with `+∞` at the zeros, the negative integers, and the
infinities, and the exact zeros at 1 and 2, where the series leaves a residue below `2 ^ -590`. -/
def lgammaReference (x : Float) : Float :=
  if x.isNaN then x
  else if x.isInf || x == 0.0 || negativeInteger x then Float.ofBits 0x7FF0000000000000
  else if x == 1.0 || x == 2.0 then 0.0
  else toFloat (lgammaFixed x Q).1 (-(Q : Int))

end TestSupport.Numerics.GammaReference
