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

## Further operations

[The further operations](Functions.lean) serve programs that evaluate a formula on intervals, and [their proofs](FunctionsProof.lean) state each result with `Encloses i x`: the interval `i` contains `x` when it is accepted.  A theorem `encloses_f` derives the relation for a result from the relation for the operands, so a proof about a chain of operations applies one theorem for each operation and needs no case analysis on acceptance.

| Operation | Result | Rejects |
|---|---|---|
| `ofInt n`, `ratio n d` | The integer `n`, exact for `\|n\| ≤ 2^53`, and an interval that contains `n / d` | A zero `d` |
| `piI` | The doubles on each side of `π` | Nothing |
| `sq a`, `imax a b` | Squares and maxima of the points | Nothing beyond a rejected operand |
| `ifPos c p q` | `p` when `c` lies above zero, `q` when it lies at or below zero | A `c` with points on both sides |
| `sinI a`, `cosI a` | Sines and cosines of the points: the library's value at the midpoint, two steps outward, widened by the distance to the endpoints | A step past the finite range |
| `twoThirds a` | `x^(2/3)` for an interval above zero: `pow` at the endpoints, four steps outward, accepted when the cubes bracket the squares of the endpoints | An interval that reaches zero, or a failed test of the cubes |
| `threeHalves a`, `sevenHalves a` | `x^(3/2)` and `x^(7/2)` as products with the square root | A lower endpoint below zero |

`encloses_ifLt` states the selection on `x < y`, computed from the sign of the difference.  `encloses_twoThirds` holds for any tables of `pow`, since the test of the cubes decides acceptance, and `encloses_sinI` and `encloses_cosI` hold for the tables `Trig.invPi` and `Trig.halfPi`, whose accuracy theorems they use.  `Contains.pos_of_lo` and its siblings turn a comparison of an endpoint with zero into the sign of every point.

## One source for a real function and its interval program

[The command `enclosure_def`](Enclose.lean) reads a chain of `let` bindings over real expressions and declares the real function `f`, the interval function `fI` in the verified compiler's dialect, and the theorem `f.encloses`: the result of `fI` encloses the result of `f` when each interval argument encloses the real argument.  The interval function replaces each real operation with the interval operation of the tables above, a literal with `ofInt` or `ratio`, and a call of another such function `g` with `gI`.  A body may end in a tuple and may bind the components of a tuple.

```lean
enclosure_def mean (xke no ecco tempa tempe templ mm0) :=
  let am := (xke / no) ^ (2 / 3 : ℝ) * tempa * tempa
  let em0 := ecco - tempe
  (am, xke / am ^ (3 / 2 : ℝ), em0, max em0 1.0e-6, mm0 + no * templ)
```

The tactic `enclose` proves the theorem.  It walks the two chains of bindings together, proves for each pair of bound values that the interval value encloses the real value, by the theorems with the label `enclose`, and continues with the two bound variables and that fact.  [The SGP4 demo](../../../Demos/Sgp4/README.md) states its model this way.

## Limits

The theorems concern real numbers between endpoint values and leave the width of a result
unbounded.  An expression in which a variable occurs more than once gives an interval wider than
its range.  `mul` and `div` reject when any of the four corner results overflows, including a
corner that the extreme does not select.  `increasing` and `decreasing` cover only functions
monotone on the whole operand, and they widen each computed value by two steps, the least
widening that a one-step accuracy theorem supports.  `sinI` and `cosI` return an interval wider
than the range by up to the width of the operand.  `enclosure_def` reads the operations of its
table and no others, and its interval function evaluates both branches of a selection.

## Internal references

- [Checked outward rounding](../Bounds/README.md)
- [Shared proof lemmas: Floating-point values and error bounds](../../../LeanExe/ProofKit/README.md#floating-point-values-and-error-bounds)
