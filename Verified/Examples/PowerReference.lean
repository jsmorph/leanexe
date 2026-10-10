import Verified.Examples.Reference

/-! Exact references for the exponentials and logarithms in bases 2 and 10 and for `pow`, computed
with Lean's integers in the fixed point of `Reference`.  `ln 10` comes from
`ln 10 = 3 ln 2 + 2 atanh (1/9)`, `2 ^ y` from the series of `exp` at `(y - k) ln 2` for the
integer `k` nearest `y`, `10 ^ y` from `Reference.exp` at `y ln 10`, the logarithms from
`Reference.log` divided by `ln 2` or `ln 10`, and `x ^ y` for a positive `x` from `Reference.exp`
at `y log x`.  Each definition states the error that its truncations leave. -/

namespace Verified.Examples.PowerReference

open Reference

/-- `ln 10 · 2 ^ W` as `3 ln 2 + 2 atanh (1/9)`, less than `2 ^ 13` units below the exact value:
`ln2Wide` is less than `2 ^ 11` units below, and `atanhInv 9 W`, with fewer than 380 terms, less
than 382. -/
def ln10Wide : Int := 3 * ln2Wide + 2 * atanhInv 9 W

/-- `ln 10 · 2 ^ q` for `q ≤ W - 13`, less than two units below the exact value. -/
def ln10 (q : Nat) : Int := ln10Wide / 2 ^ (W - q)

/-- `2 ^ y` as `(v, s)` for `v · 2 ^ s`, for `y = x · 2 ^ -q` with `q ≤ 500`: `y = k + f` with `k`
the integer nearest `y`, and `2 ^ f = exp (f ln 2)` from `Reference.expFixed` at `|f ln 2| ≤ 0.35`.
`ln 2` and the truncated product leave the argument within two units, and the series, with at most
120 terms, within `4 n + 8`, so that `v · 2 ^ s` lies within a relative `2 ^ (10 - q)` of `2 ^ y`,
since `2 ^ f ≥ 0.7`. -/
def exp2 (x : Int) (q : Nat) : Int × Int :=
  let one : Int := 2 ^ q
  let k := (2 * x + one) / (2 * one)
  (expFixed ((x - k * one) * ln2 q / one) q, k - q)

/-- `10 ^ y` as `(v, s)` for `v · 2 ^ s`, for `y = x · 2 ^ -q` with `|y| ≤ 400` and `q ≤ 500`, from
`Reference.exp` at `y ln 10`, whose fixed-point value lies within two units of the exact one, so
that `v · 2 ^ s` lies within a relative `2 ^ (14 - q)` of `10 ^ y`. -/
def exp10 (x : Int) (q : Nat) : Int × Int :=
  exp (x * ln10Wide / 2 ^ W) q

/-- `log2 (m · 2 ^ e) · 2 ^ q` for `m > 0` and `q ≤ 500`, as `Reference.log` divided by `ln 2`,
within `2 ^ 14` units, and within `2 ^ 10` near 1, where `Reference.log` errs by less than
`2 ^ 9` units. -/
def log2 (m : Nat) (e : Int) (q : Nat) : Int :=
  log m e q * 2 ^ q / ln2 q

/-- `log10 (m · 2 ^ e) · 2 ^ q` for `m > 0` and `q ≤ 500`, as `Reference.log` divided by `ln 10`,
within `2 ^ 13` units, and within `2 ^ 9` near 1. -/
def log10 (m : Nat) (e : Int) (q : Nat) : Int :=
  log m e q * 2 ^ q / ln10 q

/-- `y log x · 2 ^ 500` for `x = m · 2 ^ e > 0` and `y = n · 2 ^ d`, truncated, from
`Reference.log` at precision 500, within `|y| · 2 ^ 13 + 1` units. -/
def powExponent (m : Nat) (e : Int) (n d : Int) : Int :=
  shift (n * log m e 500) d

end Verified.Examples.PowerReference
