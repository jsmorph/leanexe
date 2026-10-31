# ScaledHypot: square root and division

## `sqrt (x * x + y * y) / s` in binary64

[The program](Program.lean) computes `sqrt (x * x + y * y) / s` in binary64, the length of the
vector `(x, y)` divided by a scale.  It uses the textbook formula, so `x * x` overflows to infinity
for `|x|` above about 1.34e154, where a library `hypot` would rescale first.  The command
`verified_compile compiled := [scaledHypot]` in [the verified compilation](Compiled.lean) compiles
`scaledHypot` into the 1,408-byte `scaledHypot.wasm` of [the module
registry](../../tests/verified/modules.txt).

## Bit-for-bit equality, overflow included

The generated `compiled.scaledHypot.implements` covers every input bit for bit, including the
overflow, a zero scale, and NaN.  The function allocates nothing, so the theorem states that
function 2 returns the bits of `sqrt (x * x + y * y) / s` without a trap, and
`compiled.scaledHypot.native` states the same of the C function of the module's translation.  The
module computes the square root and the quotient with `f64.sqrt` and `f64.div`, and the ProofKit
lemmas `F64Bits.toBits_sqrt` and `F64Bits.toBits_div` equate Lean's operations with Talos's
semantics of those instructions on the bits of all inputs.

| Theorem | Statement |
|---------|-----------|
| `compiled.scaledHypot.implements` | Function 2 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns the bits of `sqrt (x * x + y * y) / s` without a trap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements `scaledHypot`. |
| `scaledHypot_file`, `scaledHypot_file_decode` | `build/verified/scaledHypot.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

The axiom reports of the file theorems, which depend on every `implements` theorem through
`compiled.bytes`, name only `propext`, `Classical.choice`, and `Quot.sound`.  [The design
document](../../docs/design.md#floating-point) describes the binary64 equality proofs.
`compiled.scaledHypot.implements` concerns the rounded computation, with no statement about its
error relative to the exact length.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.ScaledHypot.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.ScaledHypot.Compiled Examples.ScaledHypot.compiled.module build/verified/scaledHypot.wasm
build/tools/leanexe-wasmtime-host call build/verified/scaledHypot.wasm scaledHypot f64 \
  f64:4613937818241073152 f64:4616189618054758400 f64:4617315517961601024
tests/verified/run.sh --cases scaledHypot
tests/native/verified.sh --module scaledHypot
```

The first commands build the verified compilation and its theorems, write the module, and call it in
the Wasmtime host, with the setup of [the repository README](../../README.md#commands).  The
arguments are 3.0, 4.0, and 5.0, and the call prints 4607182418800017408, the bits of 1.0.  [The
verified driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean), with
special values, arbitrary bit patterns, and a zero scale, in Wasmtime against native Lean, and [the
native driver](../../tests/native/verified.sh) runs them on the module's translation to C, compiled
with CompCert.  The cases state that a call allocates no block.

## Related examples

[`Axpy`](../Axpy/README.md) has the same structure with multiplication and addition.
[`Binary32`](../Binary32/README.md) has `hypot32`, the unscaled length in binary32.  The Euler
solvers in [`Euler`](../../Demos/Euler/README.md) use square roots for sound speeds, with outward-rounded
bounds in the reconstructed solver.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019.
- J. L. Blue, "A Portable Fortran Program to Find the Euclidean Norm of a Vector," *ACM Transactions
  on Mathematical Software* 4(1):15–23, 1978.
