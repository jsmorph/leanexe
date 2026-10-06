# ScaledHypot: square root and division

## What it is

[The program](Program.lean) computes `sqrt (x * x + y * y) / s` in binary64, the length of the
vector `(x, y)` divided by a scale.  It uses the textbook formula, so `x * x` overflows to infinity
for `|x|` above about 1.34e154, where a library `hypot` would rescale first.  [The module
definition](Module.lean) compiles `scaledHypot` into the 1,384-byte `scaledHypot.wasm`.

## What it shows

The theorem covers every input bit for bit, including the overflow, a zero scale, and NaN.  The
compiled code uses `f64.sqrt` and `f64.div`, and the ProofKit lemmas `F64Bits.toBits_sqrt` and
`F64Bits.toBits_div` equate them with Lean's operations on the bits of all inputs.  The proof has
the same form as that of [`Axpy`](../Axpy/README.md).

| Theorem | Statement |
|---------|-----------|
| `scaledHypot_implements` | Function 2 of `scaledHypot.module` implements `scaledHypot`: from any store that satisfies the runtime invariant, a call returns the bits of `sqrt (x * x + y * y) / s` or stops at `unreachable`. |
| `scaledHypot_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `scaledHypot`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  [The design document](../../docs/design.md#floating-point)
describes the binary64 equality proofs.  The theorem concerns the rounded computation, with no
statement about its error relative to the exact length.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.ScaledHypot.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.ScaledHypot.Module Examples.ScaledHypot.scaledHypot.module \
  build/scaledHypot/scaledHypot.wasm
build/tools/leanexe-wasmtime-host call build/scaledHypot/scaledHypot.wasm scaledHypot f64 \
  f64:4613937818241073152 f64:4616189618054758400 f64:4617315517961601024
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The arguments are 3.0, 4.0, and 5.0, and the
call prints 4607182418800017408, the bits of 1.0.
[`tests/modules/run.sh`](../../tests/modules/run.sh) compares 83 cases of [`Cases.lean`](Cases.lean)
with native Lean, with special values, arbitrary bit patterns, and a zero scale.

## Related examples

[`Axpy`](../Axpy/README.md) has the same structure with multiplication and addition.
[`Binary32`](../Binary32/README.md) has `hypot32`, the unscaled length in binary32.  The Euler
solvers in [`Euler`](../Euler/README.md) use square roots for sound speeds, with outward-rounded
bounds in the reconstructed solver.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019, which requires a correctly rounded
  square root.
- J. L. Blue, "A Portable Fortran Program to Find the Euclidean Norm of a Vector," *ACM Transactions
  on Mathematical Software* 4(1):15–23, 1978, on computing the length without overflow.
