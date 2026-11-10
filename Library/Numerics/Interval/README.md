# Interval arithmetic

[The native operations](Program.lean) compute with closed intervals whose endpoints are binary64
values.  An `Interval` holds a status word and the endpoints `lo` and `hi`, with status zero for
an accepted interval and status one for rejection.  Every operation rejects when an operand is
rejected or when one of its [checked outward-rounded operations](../Bounds/README.md) rejects, so
a chain of operations needs one test of the final status.

| Operation | Result | Rejects |
|---|---|---|
| `make lo hi` | `[lo, hi]` | A nonfinite endpoint, or `lo > hi` |
| `point x` | `[x, x]` | A nonfinite `x` |
| `add`, `sub`, `mul` | Sum, difference, and product, each endpoint rounded outward | An endpoint that overflows |
| `neg` | `[-hi, -lo]`, exact | Nothing beyond a rejected operand |
| `div a b` | Quotient by an interval with `0 < b.lo` or `b.hi < 0` | A divisor that holds zero, or an endpoint that overflows |
| `sqrt` | Square roots of the endpoints, rounded outward | A lower endpoint below zero, the encoding of `-0` excepted |
| `abs` | Absolute values of the interval's points, exact | Nothing beyond a rejected operand |
| `clamp a lo hi` | The part of `a` between finite `lo` and `hi` | A nonfinite bound |
| `increasing a flo fhi` | Image of `a` under an increasing function, from its computed values at the two ends | A step past the finite range |
| `decreasing a flo fhi` | Image of `a` under a decreasing function | A step past the finite range |

`mul` and `div` take the smallest of the four corner results rounded down and the largest of the
four rounded up, eight checked operations for each call.  `increasing` and `decreasing` take the
floats that the calling program computed with a library function, such as
`increasing a (exp a.lo) (exp a.hi)`, and move each two steps outward with `outward2`.  The
library functions take their tables as parameters, so the call stays in the program that owns the
tables.

## Theorems

[The soundness proofs](Proof.lean) state each result with `Contains i x`: the interval `i` has
status zero, its endpoints are finite, and the real `x` lies between their values.  Each theorem
takes an accepted result and gives the acceptance of the operands and the inclusion of the real
result for every real point of the operands.  `make` and `clamp` accept records that no operation
produces, such as an accepted status with `lo > hi`, and such a record contains no real number, so
the theorems hold for it without content.

| Theorem | Conclusion for an accepted result |
|---|---|
| `make_sound` | The endpoints are finite and ordered, and `make lo hi` contains every real between their values. |
| `point_sound` | `point x` contains the value of `x`. |
| `add_sound`, `sub_sound`, `mul_sound` | The result contains `x + y`, `x - y`, or `x * y` for `x` in `a` and `y` in `b`. |
| `neg_sound`, `abs_sound` | The result contains `-x` or the absolute value of `x` for `x` in `a`. |
| `div_sound` | For `x` in `a` and `y` in `b`, `y` is not zero and the result contains `x / y`. |
| `sqrt_sound` | For `x` in `a`, `x` is not negative and the result contains its square root. |
| `clamp_sound` | The result contains every `x` in `a` between the values of the bounds. |
| `increasing_sound`, `decreasing_sound` | For a real function monotone on `[a.lo, a.hi]` and floats within one step of the nearest-even rounding of its values at the two ends, the result contains `f x` for `x` in `a`. |

[The step lemmas](Steps.lean) supply the bound that `increasing_sound` and `decreasing_sound`
use.  `F64SignedRounding.WithinSteps 1 y w` places the word `w` within one position of the
nearest-even reference of `y` on the ordered line of doubles.  `upper_of_position` and
`lower_of_position` state that a finite word above the reference's position has a value of at
least `y` and that one below it has a value of at most `y`, and `position_nextUp` and
`position_nextDown` state that the adjacent words of a finite word lie one position away.
`two_up` and `two_down` combine them for two steps.  The accuracy theorems of the library's `sin`,
`cos`, `asin`, `acos`, `atan`, `erf`, and `erfc` have this form, and
`F64SignedRounding.within_of_nonneg` derives it from the theorem of `exp`.

[The compiled module](Compiled.lean) supplies execution proofs for every operation, with
[a flat encoding](Encoding.lean) of the status and the endpoints as `UInt64 × Float × Float`, and
[the file theorems](File.lean) identify `build/verified/libinterval.wasm`.

## Limits

The theorems concern real numbers between endpoint values and leave the width of a result
unbounded.  An expression in which a variable occurs more than once gives an interval wider than
its range.  `mul` and `div` reject when any of the four corner results overflows, including a
corner that the extreme does not select.  The function enclosures cover only functions monotone on
the whole operand, and they widen each computed value by two steps, the least widening that a
one-step accuracy theorem supports.

## Internal references

- [Checked outward rounding](../Bounds/README.md)
- [Shared proof lemmas: Floating-point values and error bounds](../../../LeanExe/ProofKit/README.md#floating-point-values-and-error-bounds)
