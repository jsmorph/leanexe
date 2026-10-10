import Verified.Examples.Reference

/-! Exact references for the inverse trigonometric functions, computed with Lean's integers in the
fixed point of `Reference`: a value at precision `q` is an integer `v` that stands for
`v · 2 ^ -q`.  `atanFixed` halves the angle twice with `atan t = 2 atan (t/(1 + √(1 + t²)))`, so
that the series `t - t³/3 + t⁵/5 - …` runs at `t ≤ tan (π/16) < 1/5`, and the others reduce to
it: `atan` of a quotient of naturals through `atan t = π/2 - atan (1/t)` above 1,
`asin x = 2 atan (x/(1 + √(1 - x²)))`, and `acos x = 2 atan √((1 - x)/(1 + x))`.  Each
definition states the error that its truncations leave. -/

namespace Verified.Examples.ArcReference

open Reference

/-- `⌊√n⌋`, by Newton's iteration from `2 ^ (⌊log₂ n⌋/2 + 1)`, which exceeds `√n`: the iterates
decrease while they exceed `⌊√n⌋` and stop at it. -/
def isqrt (n : Nat) : Nat := Id.run do
  if n == 0 then return 0
  let mut x := 2 ^ (Nat.log2 n / 2 + 1)
  let mut y := (x + n / x) / 2
  while y < x do
    x := y
    y := (x + n / x) / 2
  return x

/-- `t/(1 + √(1 + t²)) · 2 ^ q` for `t · 2 ^ -q` with `t ≤ 2 ^ q`, the tangent of half the angle,
truncated.  The square root lies less than a unit below its exact value and moves the quotient by
less than `t/2 ^ q ≤ 1` unit, so that the result lies within one unit of the exact value. -/
def halfAngle (t q : Nat) : Nat :=
  let one := 2 ^ q
  t * one / (one + isqrt (one * one + t * t))

/-- `arctan (t · 2 ^ -q) · 2 ^ q` for `t ≤ 2 ^ q`, within `16 n + 18` units of the exact value for
`n` terms of the series, which is below `2 ^ 14` units for `q ≤ 3000`.  Two half-angle steps leave
the argument within 1.5 units of `tan (θ/4)`, since the derivative of the step is at most 1/2, and
below `1/5`.  As in `Reference.atanhFixed`, each power lies less than 2.1 units below its exact
value and each term less than 3.1, and the terms omitted, alternating and decreasing, sum to less
than 2.1 units, so that the series lies within `3.1 n + 3.6` units of the arctangent of the exact
reduced argument.  The factor 4 multiplies these errors. -/
def atanFixed (t q : Nat) : Int := Id.run do
  let one := 2 ^ q
  let t := halfAngle (halfAngle t q) q
  let t2 := t * t / one
  let mut total : Int := 0
  let mut term := t
  let mut n := 1
  let mut sign : Int := 1
  while term != 0 do
    total := total + sign * (term / n : Nat)
    term := term * t2 / one
    n := n + 2
    sign := -sign
  return 4 * total

/-- `arctan (num/den) · 2 ^ q` for `den > 0` and `q ≤ W - 15`: the series at `num/den` up to 1,
and `π/2 - arctan (den/num)` above, within `16 n + 21` units for `n` terms.  The quotient's
truncation adds a unit and `π/2` from `Reference.pi` two more. -/
def atanQuotient (num den q : Nat) : Int :=
  if num ≤ den then atanFixed (num * 2 ^ q / den) q
  else pi (q + 1) / 4 - atanFixed (den * 2 ^ q / num) q

/-- `arcsin (x · 2 ^ -q) · 2 ^ q` for `0 ≤ x ≤ 2 ^ q`, as `2 atan (x/(1 + √(1 - x²)))`.  The
square root and the quotient leave the argument within two units of the exact one, so that the
value lies within `32 n + 40` units for `n` terms of the series. -/
def asinFixed (x q : Nat) : Int :=
  let one := 2 ^ q
  2 * atanFixed (x * one / (one + isqrt (one * one - x * x))) q

/-- `arccos (x) · 2 ^ q` for `x = s · 2 ^ -(2 q)` with `|s| < 2 ^ (2 q)` and `q ≤ W - 14`, as
`2 atan √((1 - x)/(1 + x))`, or `π - 2 atan √((1 + x)/(1 - x))` for negative `x`, so that the
series runs at an argument up to 1.  `a = (1 - x) · 2 ^ (2 q)` and `b = (1 + x) · 2 ^ (2 q)` are
exact, the truncated quotient and square root leave the argument within two units, and the value
lies within `32 n + 44` units for `n` terms of the series. -/
def acosFixed (s : Int) (q : Nat) : Int :=
  let a := (2 ^ (2 * q) - s).toNat
  let b := (2 ^ (2 * q) + s).toNat
  if s ≥ 0 then 2 * atanFixed (isqrt (a * 2 ^ (2 * q) / b)) q
  else pi q - 2 * atanFixed (isqrt (b * 2 ^ (2 * q) / a)) q

end Verified.Examples.ArcReference
