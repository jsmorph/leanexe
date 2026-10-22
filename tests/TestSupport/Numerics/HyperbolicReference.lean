import TestSupport.Numerics.ArcReference

/-! Exact references for the hyperbolic functions and their inverses, computed with Lean's
integers in the fixed point of `Reference`.  `sinh` and `cosh` come from `Reference.expm1`, which
keeps its relative accuracy near 0, and the inverses from `Reference.log` and
`Reference.atanhFixed`, with square roots from `ArcReference.isqrt`.  Each definition states the
error that its truncations leave. -/

namespace TestSupport.Numerics.HyperbolicReference

open Reference ArcReference

/-- `sinh (y) · 2 ^ q` for `y = x · 2 ^ -q`, `0 ≤ y < 1100`, and `q ≤ 2000`, as
`(E + E/(E + 1))/2` with `E = expm1 y`.  `E` lies within a relative `2 ^ (15 - q)/min 1 y` of its
exact value, the quotient within twice that plus a unit, and `sinh y ≥ y`, so that the value lies
within a relative `2 ^ (17 - q)/min 1 y` plus two units. -/
def sinhFixed (x q : Nat) : Int :=
  let e := expm1 x q
  let one : Int := 2 ^ q
  (e + e * one / (e + one)) / 2

/-- `cosh (y) · 2 ^ q` for `y = x · 2 ^ -q`, `0 ≤ y < 1100`, and `q ≤ 2000`, as
`1 + E²/(2 (E + 1))` with `E = expm1 y`, within a relative `2 ^ (17 - q)` plus a unit, since the
term `E²/(2 (E + 1))` is below `E` and `cosh y ≥ max 1 (E/2)`. -/
def coshFixed (x q : Nat) : Int :=
  let e := expm1 x q
  let one : Int := 2 ^ q
  one + e * e / (2 * (e + one))

/-- `asinh (y) · 2 ^ q` for `y = x · 2 ^ -q ≥ 0` and `q ≤ 500`.  Below `0.4` it is
`2 atanh (y/(1 + √(1 + y²)))`, whose argument is below `1/5`, and `Reference.atanhFixed` leaves
less than `2 n + 6` units for `n` terms.  From `0.4` on it is `log (y + √(y² + 1))` from
`Reference.log` of the truncated sum, which lies within two units of the exact one, so that the
value lies within `2 ^ 13 + 2` units. -/
def asinhFixed (x q : Nat) : Int :=
  let one := 2 ^ q
  if 5 * x < 2 * one then 2 * atanhFixed (x * one / (one + isqrt (one * one + x * x))) q
  else log (x + isqrt (x * x + one * one)) (-(q : Int)) q

/-- `acosh (y) · 2 ^ q` for `y = x · 2 ^ -q ≥ 1` and `q ≤ 500`, as `log (y + √(y² - 1))` from
`Reference.log` of the truncated sum, within `2 ^ 13 + 2` units.  Near 1 the logarithm's error is
below `2 ^ 9 + 2` units, and `acosh y ≥ √(2 (y - 1))`. -/
def acoshFixed (x q : Nat) : Int :=
  let one := 2 ^ q
  log (x + isqrt (x * x - one * one)) (-(q : Int)) q

/-- `atanh (y) · 2 ^ q` for `y = m · 2 ^ e` with `1/5 < y < 1`, `e < 0`, and `q ≤ 500`, as
`(log (1 + y) - log (1 - y))/2` from `Reference.log` of the exact `1 ± y`, within `2 ^ 13 + 1`
units.  Up to `1/5`, `Reference.atanhFixed` gives `atanh` directly. -/
def atanhLog (m : Nat) (e : Int) (q : Nat) : Int :=
  (log (2 ^ (-e).toNat + m) e q - log (2 ^ (-e).toNat - m) e q) / 2

end TestSupport.Numerics.HyperbolicReference
