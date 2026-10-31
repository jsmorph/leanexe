# Piecewise: float comparisons and selection

## A piecewise function of `x`

[The program](Program.lean) is a piecewise function of `x` with the bounds `lo` and `hi`: 0 when `x
== lo`, `-(lo - x) * 0.5` below `lo`, `|hi - x| + 1.5` at or above `hi`, and `max lo (min x hi)` in
between.  It exists to exercise the operations it contains: float equality, `<`, `≤`, nested `if`,
negation, absolute value, `min`, and `max`.  `verified_compile compiled := [piecewise]` in [the
verified compilation](Compiled.lean) compiles the definition into the 1,567-byte `piecewise.wasm` of
[the module registry](../../tests/verified/modules.txt).

## Negation, `abs`, `min`, and `max` in Lean and WebAssembly

Lean and WebAssembly define negation, `abs`, `min`, and `max` differently.  Lean's negation and
`abs` return the canonical NaN for a NaN input, where WebAssembly's `f64.neg` changes only the sign
bit, and Lean's `min` and `max` choose an operand by `≤`, where `f64.min` and `f64.max` return NaN
for a NaN operand and order `-0` below `+0`.  The verified compiler translates negation to
`-0.0 - x` and `abs` to `f64.abs`, and the reflector reads `min a b` and `max a b` as conditionals on
`a ≤ b`.  [The design document](../../docs/design.md#floating-point) lists the differences and
their compiled forms.

The function allocates nothing, so the generated `compiled.piecewise.implements` states that
function 2 returns the bits of `piecewise x lo hi` without a trap.  The generated
`compiled.piecewise.native` states the same of the C function of the module's translation.  The
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

| Theorem | Statement |
|---------|-----------|
| `compiled.piecewise.implements` | Function 2 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns the bits of `piecewise x lo hi` without a trap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements `piecewise`. |
| `piecewise_file`, `piecewise_file_decode` | `build/verified/piecewise.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Piecewise.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Piecewise.Compiled Examples.Piecewise.compiled.module build/verified/piecewise.wasm
build/tools/leanexe-wasmtime-host call build/verified/piecewise.wasm piecewise f64 \
  f64:13830554455654793216 f64:0 f64:4607182418800017408
tests/verified/run.sh --cases piecewise
tests/native/verified.sh --module piecewise
```

The commands build the verified compilation and its theorems, write the module, call it in the
Wasmtime host, and run the tests, with the setup of [the repository README](../../README.md#commands).
The arguments are -1.0, 0.0, and 1.0, and the call prints 13826050856027422720, the bits of -0.5.
[The verified driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean),
among them `x == lo` with signed zeros and NaN in each argument, in Wasmtime against native Lean,
and [the native driver](../../tests/native/verified.sh) runs them on the module's translation to C,
compiled with CompCert.  The cases state that a call allocates no block.

## Related examples

[`Binary32`](../Binary32/README.md) has `piecewise32`, the same function on `Float32`.
[`Bools`](../Bools/README.md) returns float comparisons as `Bool` values.  The LTG entries
[`float-arithmetic`](../../ltg/entries/float-arithmetic/README.md) and
[`binary32-arithmetic`](../../ltg/entries/binary32-arithmetic/README.md) hold proof guidance for
binary64 and binary32 operations.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019.
- WebAssembly Core Specification,
  [Numerics](https://webassembly.github.io/spec/core/exec/numerics.html).
