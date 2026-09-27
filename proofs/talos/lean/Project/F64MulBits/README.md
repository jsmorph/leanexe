# Binary64 Multiplication Example

This example is the first end-to-end quantitative floating-point proof for a
LeanExe-generated WebAssembly program.  The public program accepts two
`UInt64` values containing IEEE-754 binary64 encodings and returns the encoding
produced by one `f64.mul`.

## Goal

Connect one small LeanExe entry to a useful numerical statement at both proof
levels used by this project:

1. give the Lean source entry a pure, proof-visible binary64 contract; and
2. prove that the WAT emitted for that entry terminates with exactly the same
   modeled result and therefore satisfies the same error bound.

For finite inputs `left` and `right` whose interpreted real magnitudes are at
most one, the result is finite and

```text
|value(result) - value(left) * value(right)| <= 2^-52.
```

The WebAssembly theorem also says that execution leaves the store unchanged.

## Approach

[`Spec.lean`](Spec.lean) defines `mulBitsModel` as the pure Talos operation
`Wasm.IEEE64.mul`.  Its source-facing specification is attached to
`LeanExe.Examples.Float64Bits.mulBits` with `spec_of` metadata.  The numerical
proof applies CodeLib's binary64 multiplication theorem to that model.

[`Program.lean`](Program.lean) is generated from the actual compiler-emitted
WAT.  The exported function keeps an integer bit-pattern ABI and executes:

```text
i64 -> f64 reinterpret
i64 -> f64 reinterpret
f64.mul
f64 -> i64 reinterpret
```

`mulBits_exact` proves fuel-independent execution of this decoded program for
all input bit patterns.  `mulBits_wat_real_error` combines exact execution with
the source-facing numerical theorem.  A separate nine-transition
`SmallStep.Steps` proof exposes every instruction, including the compiler's
local-result epilogue and function completion.

## Result

The checked public theorems establish:

- exact result bits: `Wasm.IEEE64.mul left right`;
- termination independent of interpreter fuel;
- preservation of the complete WebAssembly store;
- finiteness under the stated finite, unit-magnitude input assumptions; and
- absolute real error at most `CodeLib.IEEE64.multiplicationEpsilon`, which is
  `2^-52`.

The public axiom reports contain only Lean's standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound`.

## Proof boundary

The source-facing theorem gives a proof-visible contract to the
compiler-recognized LeanExe intrinsic.  It does **not** prove that Lean's native
`Float` evaluator implements Talos's model.  Native floating-point execution is
used only by executable regression tests.

The WAT result is stronger and direct: Talos decodes the WAT freshly generated
from the registered source entry, and Lean proves its exact execution under
Talos's pure WebAssembly and IEEE-754 semantics.  No native floating-point
evaluation appears in that proof.

## Check

From the repository root:

```sh
tools/talos-proof.js check f64_mul_bits
```

The proof workspace and compiler are checked with Lean `4.34.0-rc2`.
