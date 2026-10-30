# Shared proof lemmas

## Memory, arrays, and execution

| Goal | Starting point and premises |
|---|---|
| Read or write a word in linear memory | [Memory facts](Memory.lean) prove read-after-write equality and preservation of reads disjoint from a write.  [Memory frames](MemoryFrame.lean) define `WritesRange`, which preserves the page count, other store fields, and bytes outside a half-open interval. |
| Relate a compiled array to its elements | [Array representation](Array.lean) supplies `UInt64Array.At`, length and element facts, and `ArrayFold.foldPrefix`.  [Prefix representation](ArrayPrefix.lean) states how much of a new array has been filled.  Pointer and size bounds keep addresses within memory. |
| Prove allocator behavior | [Fixed-array allocation](FixedArrayAllocate.lean) supplies `program_spec_runs` for 32-bit memory, requests of at most `2^32` bytes, and a cap of at most 65,535 pages.  It covers free-list reuse and bump allocation, requiring room when `aborts = false`.  [The pipeline allocation rules](../Pipeline/Allocation.lean) prove preservation of `Heap.At`, borrowed arrays, and owned objects. |
| Recover locals after replacing the operand stack | [Local frames](Frame.lean) prove that replacing `Locals.values` preserves parameters, internal locals, and `get`.  `parameter_getElem_of_get` and `internal_getElem_of_get` turn combined-index reads into facts about the corresponding lists. |
| Release a recursive value | [Tree release](ReleaseTree.lean) proves that the runtime traversal through masked child slots frees the owned records and preserves the caller's other regions.  The value's owned blocks and their separation supply the premises. |
| Carry alignment through an execution | [Aligned-run definitions](AlignedDefs.lean) follow Talos's execution and require an in-bounds 64-bit access to have an address divisible by eight.  [Flagged rules](AlignedFlag.lean) specialize to ordinary `wp` at `strict = false` and aligned `wpA` at `strict = true`. |
| Establish partial correctness of a process loop | [Partial-loop rules](PartialLoop.lean) use `pwp`, which constrains runs that finish within their fuel.  A termination argument is an additional obligation of the total-process proof. |

The [pipeline heap predicates](../Pipeline/Runtime.lean) combine `UInt64Array.At` with block
bounds and free-list separation in `Heap.Borrowed` and `Heap.Owned`.
[The call statement](../Pipeline/Implements.lean) includes argument representation, separation,
and preservation of the caller's regions.

## Floating-point values and error bounds

[The binary64 wrapper](Float64.lean), [binary32 facts](F32Bits.lean), and
[binary64 bit facts](F64Bits.lean) connect Lean floating-point operations with their raw-word
models.

| Goal | Starting point |
|---|---|
| Track rounded arithmetic against real values | [Binary64 approximation](F64Approx.lean) defines `Approx w v e` and `FApprox x v e`.  An operation propagates input errors and adds a rounding bound under magnitude, finiteness, and divisor premises. |
| State an error in representable steps | [Signed rounding](F64SignedRounding.lean) defines the nearest-even reference and `WithinSteps`.  The predicate excludes NaN results and counts both signed zeros at the same position. |
| Prove an exact arithmetic step | [Exactness rules](F64Exact.lean), [exact products](F64ExactProduct.lean), and [Sterbenz's lemma](F64Sterbenz.lean) supply conditions under which the rounded value equals the real operation. |
| Prove a checked arithmetic result bounds the exact value | [Outward operations](F64Outward.lean) select the next word above or below the rounded result and reject a nonfinite endpoint.  [Their specifications](F64OutwardSpec.lean) prove that status 0 gives a finite upper or lower bound on the exact real operation. |
| Bound a final rounded sum or difference by one step | [Nearest-rounding bounds](F64RoundNearest.lean) supply `add_within` and `sub_within`, with `FApprox` bounds for both inputs.  They require an error bound before the final rounding below one spacing in a chosen normal binade, a target magnitude at least that error above the binade's start, and `\|y\| < 2^1022`. |
| Convert relative error to a bound in representable steps | [Relative bounds](F64RelativeSteps.lean) supply `within_steps_relative`: for a finite word `c`, `1 ≤ m ≤ 64`, and `\|y\| ≥ (17/16) * 2^-1022`, the bound `\|value c - y\| ≤ (m + 3/8) * 2^-53 * \|y\|` gives `WithinSteps m y c`. |
| Bound a function that returns its argument | [`within_one_of_self`](F64WithinSelf.lean) proves `WithinSteps 1 y x` for a finite input word `x`, `0 ≤ ρ ≤ 2^-53`, and `\|value x - y\| ≤ ρ * \|value x\|`. |

The [binary64 error-tracking entry](../../VKB/entries/float-error-tracking/README.md) explains
how finished numerical proofs discharge magnitude premises and choose a final rounding rule.
The [numerical guides](../../index.md#6-elementary-and-special-functions) state each function's
domain, exceptional results, and proved allowance.

## Polynomial checks and function bounds

[The polynomial checker](PolyBound.lean) bounds a polynomial with rational coefficients over
a rational interval by shifting it to the midpoint and bisecting when needed.  `check_sound`
turns an accepted calculation into a bound for every real input in the interval.
[Interval and weighted checks](PolyChecks.lean) combine checks over subintervals with `Covers`
and derive `abs (A x) ≤ ε * W x` from two one-sided polynomial bounds.  `sub_div_le` turns
`abs (f * q - p) ≤ e * q` into `abs (f - p / q) ≤ e` when `q > 0`.

[Taylor remainders](TaylorRemainder.lean) bound the errors of the sine, cosine, and exponential
polynomials for `abs x ≤ 1`, with a positive truncation count for the exponential.  The
bounds for `log (1 + x)` and `atan x` require `abs x < 1`.
[Error-function theory](RealErf.lean) defines `erf`, `erfc`, and `erfcx`, proves their derivatives,
and bounds `erfc` and `erfcx` by alternating asymptotic sums for positive arguments.
[Gamma identities](GammaBasic.lean) give recurrence identities away from the poles and
reflection identities at noninteger arguments.

Generators choose coefficients, interval divisions, and bounds.  Lean's kernel checks the
proofs of the generated claims, as
[the arcsine proof](../../Library/Numerics/Float64/Asin/README.md#proof) illustrates.
