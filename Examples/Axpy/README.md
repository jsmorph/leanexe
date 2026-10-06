# Axpy: binary64 arithmetic bit for bit

## What it is

[The program](Program.lean) computes `a * x + y` on Lean `Float` values, IEEE 754 binary64, with two
roundings: one after the product and one after the sum.  The name comes from the BLAS routine
`axpy`, which applies the same operation to vectors.  [The module definition](Module.lean) compiles
`axpy` into the 1,370-byte `axpy.wasm`, which exports `axpy` with three `f64` parameters and an
`f64` result.

## What it shows

The theorem states that the module returns the bit pattern of Lean's result for every input,
including NaN, the infinities, signed zeros, and subnormal values.  ProofKit proves that Lean's
binary64 addition, subtraction, multiplication, division, and square root equal Talos's `IEEE64`
functions on bit patterns for all inputs, and the proof of `axpy_implements` rewrites with those
lemmas.  Lean's float model has one NaN, the positive quiet NaN `0x7FF8000000000000`, and the
WebAssembly deterministic profile requires the same, which the Wasmtime host enables through
Cranelift's NaN canonicalization.

| Theorem | Statement |
|---------|-----------|
| `axpy_implements` | Function 2 of `axpy.module` implements `axpy`: from any store that satisfies the runtime invariant, a call returns the bits of `a * x + y` or stops at `unreachable`. |
| `axpy_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `axpy`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  [The design document](../../docs/design.md#floating-point)
describes the binary64 equality proofs and the three places where Lean's and WebAssembly's float
operations differ.  None of the three occurs in this program.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Axpy.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Axpy.Module Examples.Axpy.axpy.module build/axpy/axpy.wasm
build/tools/leanexe-wasmtime-host call build/axpy/axpy.wasm axpy f64 \
  f64:4611686018427387904 f64:4613937818241073152 f64:4607182418800017408
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The host takes and prints floats as bit patterns
in decimal: the arguments are 2.0, 3.0, and 1.0, and the call prints 4619567317775286272, the bits
of 7.0.  [`tests/modules/run.sh`](../../tests/modules/run.sh) compares 80 cases of
[`Cases.lean`](Cases.lean) with native Lean, with special values among the arguments.

## Related examples

[`ScaledHypot`](../ScaledHypot/README.md) adds square root and division, and
[`Piecewise`](../Piecewise/README.md) adds comparisons, negation, `abs`, `min`, and `max`.
[`Binary32`](../Binary32/README.md) has `axpy32`, the same function on `Float32`.  The LTG entry
[`float-arithmetic`](../../ltg/entries/float-arithmetic/README.md) describes the rules for float
expressions.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019.
- C. L. Lawson, R. J. Hanson, D. R. Kincaid, and F. T. Krogh, "Basic Linear Algebra Subprograms for
  Fortran Usage," *ACM Transactions on Mathematical Software* 5(3):308–323, 1979.
- WebAssembly Core Specification,
  [numerics](https://webassembly.github.io/spec/core/exec/numerics.html) and [the deterministic
  profile](https://webassembly.github.io/spec/core/appendix/profiles.html).
