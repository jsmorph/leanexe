# Piecewise: float comparisons and selection

## What it is

[The program](Program.lean) is a piecewise function of `x` with the bounds `lo` and `hi`: 0 when `x
== lo`, `-(lo - x) * 0.5` below `lo`, `|hi - x| + 1.5` at or above `hi`, and `max lo (min x hi)` in
between.  It exists to exercise the operations it contains: float equality, `<`, `≤`, nested `if`,
negation, absolute value, `min`, and `max`.  [The module definition](Module.lean) compiles
`piecewise` into the 1,479-byte `piecewise.wasm`.

## What it shows

Three of these operations differ between Lean and WebAssembly.  Lean's negation and `abs` return the
canonical NaN for a NaN input, where WebAssembly's `f64.neg` changes only the sign bit, and Lean's
`min` and `max` choose an operand by `≤`, where `f64.min` and `f64.max` return NaN for a NaN operand
and order `-0` below `+0`.  The compiler translates negation to `-0.0 - x`, `abs` to `f64.abs`, and
`min` and `max` to a comparison and a selection, and the ProofKit lemmas `F64Bits.toBits_neg`,
`toBits_abs`, `toBits_min`, and `toBits_max` prove that these forms give Lean's bits.

| Theorem | Statement |
|---------|-----------|
| `piecewise_implements` | Function 2 of `piecewise.module` implements `piecewise`: from any store that satisfies the runtime invariant, a call returns the bits of `piecewise x lo hi` or stops at `unreachable`. |
| `piecewise_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `piecewise`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  The comparisons rest on `F64Bits.lt_iff`, `le_iff`, and
`beq_eq`, which equate Lean's comparisons with IEEE comparisons of the bits.  [The design
document](../../docs/design.md#floating-point) lists the three differences and their compiled forms.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Piecewise.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Piecewise.Module Examples.Piecewise.piecewise.module build/piecewise/piecewise.wasm
build/tools/leanexe-wasmtime-host call build/piecewise/piecewise.wasm piecewise f64 \
  f64:13830554455654793216 f64:0 f64:4607182418800017408
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The arguments are -1.0, 0.0, and 1.0, and the
call prints 13826050856027422720, the bits of -0.5.
[`tests/modules/run.sh`](../../tests/modules/run.sh) compares 90 cases of [`Cases.lean`](Cases.lean)
with native Lean, including `x == lo` with signed zeros and NaN in each argument.

## Related examples

[`Binary32`](../Binary32/README.md) has `piecewise32`, the same function on `Float32`, with the
binary32 counterparts of these lemmas.  [`Bools`](../Bools/README.md) returns float comparisons as
`Bool` values.  The LTG entries [`float-arithmetic`](../../ltg/entries/float-arithmetic/README.md)
and [`binary32-arithmetic`](../../ltg/entries/binary32-arithmetic/README.md) describe the rules.

## References

- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019, for the comparison predicates and
  the sign-bit operations.
- WebAssembly Core Specification,
  [numerics](https://webassembly.github.io/spec/core/exec/numerics.html), for `fneg`, `fabs`,
  `fmin`, and `fmax`.
