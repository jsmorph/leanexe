# Runtime-length guarded binary64 dot product

## Goal

This example takes two runtime `Array UInt64` values whose words encode
binary64 numbers.  It demonstrates that LeanExe can compile a genuine
variable-length numerical loop and that Talos can prove the same quantitative
floating-point statement for the exact generated WAT.

The public result contains a status word and result bits.  Status zero denotes
an equal-length dot product.  Status one denotes unequal lengths, and a
rejected result has zero payload bits.

## Approach

`LeanExe.Examples.Float64Bits.dotCheckedBits` first checks equal lengths and
handles the empty input explicitly.  A nonempty input seeds the accumulator
with one modeled binary64 multiplication, then indexes both arrays in a
runtime loop.  Each remaining pair performs one multiplication and one
addition, giving exactly `2*n - 1` rounded operations for a nonempty input and
positive zero for the empty dot product.

The proof is organized in three layers:

1. relate the two array views and generated loop to a list of Talos binary64
   pairs;
2. reuse Talos's absolute-error, gamma-times-mass, and condition-number dot
   theorems; and
3. prove fuel-independent execution of the decoded compiler-generated WAT,
   including its array representation, loop invariant, result words, and
   memory/store frame.

## Result

The source program and its pure Talos numerical contract are implemented.
Runtime regression cases cover empty, singleton, multi-element,
unequal-length, and out-of-theorem-domain inputs.  The checked source theorems
are:

- `dotCheckedBits_source_absolute_error`, with the full primitive absolute
  budget;
- `dotCheckedBits_source_gamma_error`, with the operation-count
  gamma-times-exact-mass bound; and
- `dotCheckedBits_source_conditioned_relative_error`, with the corresponding
  condition-number bound for a nonzero exact result.

They state all finiteness, unit-bound, aggregate-headroom, normal-or-zero,
gamma-pole, and nonzero-exact-result assumptions explicitly.  Their axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.  The
compiler-generated WAT is frozen as `Project.F64DotCheckedBits.Program`, and
its entry and four runtime helpers build against the exact decoded Talos
module.  The execution layer proves fuel-independent, store-preserving
behavior for every path: unequal lengths reject, equal empty arrays return
positive zero, and equal nonempty arrays execute the modeled `dot64List`
multiply-add recurrence.  Both seed reads and both reads in every iteration
use the reusable checked-load theorem; counter wraparound is excluded and an
explicit decreasing measure proves termination.

The public WAT theorems now carry all three source numerical conclusions over
that exact execution: the primitive absolute budget, the operation-count
gamma-times-mass bound, and the conditioned relative-error bound.  Thus the
same finite/error statements are proved first for the LeanExe source model and
then for the decoded compiler-generated WAT.  Their axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

Native floating-point execution is used only for regression tests.  Accepted
theorems use Talos's pure IEEE-754 model and WebAssembly semantics.

## Check

`test/f64_dot.js` is the focused source/runtime regression.  It compiles only
this entry, runs the representative array cases, and checks the extracted IR
and generated WAT operation sites.  Set `LEANEXE_F64_DOT_PREBUILT=1` when the
three artifacts have already been produced through the repository's serial
Lean runner.
