import TestSupport.Numerics.ArcReference

/-! Exact references for `erf` and `erfc`, computed with Lean's integers in the fixed point of
`Reference`.  Below 6, `erf x = (2/√π) x e^(-x²) S` with the series of positive terms
`S = Σ (2 x²)^n/(1 · 3 ⋯ (2 n + 1))`, which converges for every `x` and has no cancellation, and
`erfc x = 1 - erf x`.  From 6 on, `erfc x = e^(-x²) K/√π` with Laplace's continued fraction
`K = 1/(x + (1/2)/(x + (2/2)/(x + (3/2)/(x + ⋯))))`, whose elements are positive, so that its
successive convergents lie on alternate sides of `K` and their difference bounds the error.  The
continued fraction runs in exact integer arithmetic after the equivalence transformation that
multiplies each level by `2 v` for `x = u/v`.  `√π` comes from `Reference.pi` and
`ArcReference.isqrt`.  Each definition states the error that its truncations leave. -/

namespace TestSupport.Numerics.ErfReference

open Reference ArcReference

/-- `√π · 2 ^ q` for `q ≤ 1193`, truncated, within two units: `Reference.pi (2 q)` lies within two
units of `π · 2 ^ (2 q)`, and the square root of a value at least `2 ^ (2 q)` moves by less than a
unit when the value moves by two. -/
def sqrtPi (q : Nat) : Nat := isqrt (pi (2 * q)).toNat

/-- `2 e^(-x²) S/√π · 2 ^ q` for `x = m · 2 ^ e` with `0 < x < 6` and `q ≤ 400`, where `erf x` is
`x` times this factor, within a relative `2 ^ (7 - q)`.  The series runs at precision `q + 64`.
Where `x² · 2 ^ (q + 64)` is not an integer, its truncation changes `S` by less than a unit.  Each
term loses less than two units to truncation and multiplies the error of the term before by
`2 x²/(2 n + 3)`, so that the error of a term stays below `2 n` units times `e^(x²) < 2 ^ 52`, the
largest ratio of a later term to an earlier one, and the at most 400 terms leave less than `2 ^ 70`
units, a relative `2 ^ -(q - 6)` since `S ≥ 1`.  `Reference.exp` adds a relative `2 ^ (13 - q - 64)`
and `sqrtPi` less. -/
def erfFactor (m : Nat) (e : Int) (q : Nat) : Int :=
  let g := q + 64
  let x2 := shift (m * m) (2 * e + g)
  let s := Id.run do
    let mut total : Int := 0
    let mut term : Int := 2 ^ g
    let mut n := 0
    while term != 0 do
      total := total + term
      term := term * (2 * x2) / 2 ^ g / (2 * n + 3)
      n := n + 1
    return total
  let (v, k) := exp (-x2) g
  shift (shift (2 * v * s) (k + g) / sqrtPi g) (-64)

/-- `√π e^(x²) erfc (x) · 2 ^ q` for `x = m · 2 ^ e` with `x ≥ 1`, from the convergents
`P_k/Q_k` of Laplace's continued fraction with the integer elements `2 v`, `2 v² (k - 1)`, and
`2 u` for `x = u/v`.  The loop stops at the first `k` for which two successive convergents differ
by at most a relative `2 ^ -(q + 2)`, which the value lies between, so that the result lies within
a relative `2 ^ -(q + 2)` plus a unit of the value.  At 6 and `q = 400` it stops after about 350
levels. -/
def erfcFraction (m : Nat) (e : Int) (q : Nat) : Nat := Id.run do
  let (u, v) : Nat × Nat := if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)
  let mut p2 : Nat := 1
  let mut p1 : Nat := 0
  let mut q2 : Nat := 0
  let mut q1 : Nat := 1
  for k in [1:100000] do
    let a := if k == 1 then 2 * v else 2 * v * v * (k - 1)
    let pk := 2 * u * p1 + a * p2
    let qk := 2 * u * q1 + a * q2
    if k ≥ 2 && (((pk * q1 : Nat) : Int) - ((p1 * qk : Nat) : Int)).natAbs * 2 ^ (q + 2) ≤
        min (pk * q1) (p1 * qk) then
      return pk * 2 ^ q / qk
    p2 := p1
    p1 := pk
    q2 := q1
    q1 := qk
  return 0

end TestSupport.Numerics.ErfReference
